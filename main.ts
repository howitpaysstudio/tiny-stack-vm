// tiny-stack-vm: an exact interpreter for make.fun's tiny stack ISA (spec: ISA.md in the bounty kit).
// Reference semantics copied exactly, awkward corners included: wrapping 32-bit arithmetic, INT_MIN / -1,
// unsigned ops read unsigned, shift counts mod 32, every trap's own exit code, output kept on a trap.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Fetch-stage facts per opcode, packed as imm*100 + pops*10 + pushes; a missing entry is not an opcode.
const T: number[] = [];
{
  const d = (b: number, i: number, p: number, q: number) => { T[b] = i * 100 + p * 10 + q; };
  d(0x00, 0, 0, 0); d(0x01, 1, 0, 1); d(0x02, 4, 0, 1); d(0x03, 0, 1, 0); // HALT PUSH8 PUSH32 POP
  d(0x04, 0, 1, 2); d(0x05, 0, 2, 2); d(0x06, 0, 2, 3); d(0x07, 0, 3, 3); // DUP SWAP OVER ROT
  for (let b = 0x10; b <= 0x1e; b++) d(b, 0, b === 0x17 || b === 0x1b ? 1 : 2, 1); // arithmetic; NEG/NOT unary
  for (let b = 0x20; b <= 0x22; b++) d(b, 0, 2, 1); // EQ LT LTU
  d(0x30, 2, 0, 0); d(0x31, 2, 1, 0); d(0x32, 2, 1, 0); d(0x33, 2, 0, 0); d(0x34, 0, 0, 0); // JMP JZ JNZ CALL RET
  d(0x40, 0, 1, 1); d(0x41, 0, 2, 0); d(0x50, 0, 1, 0); d(0x51, 0, 1, 0); d(0x52, 0, 0, 1); d(0x53, 0, 1, 0);
}

// Runs one program to its end: the bytes it wrote and the code it ended with (a trap's code counts).
function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const buf = new Uint8Array(65_536);
  let sp = 0, csp = 0, blen = 0, pc = 0, steps = 0, ipos = 0;
  const n = prog.length;
  const fin = (code: number): { out: Uint8Array; code: number } => ({ out: buf.slice(0, blen), code });

  for (;;) {
    // Step order: step limit, pc in range, known opcode, immediate fits, stack needs, then execute.
    if (steps >= 1_000_000) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = prog[pc];
    const t = T[op];
    if (t === undefined) return fin(5);
    const imm = Math.floor(t / 100), pops = Math.floor(t / 10) % 10, pushes = t % 10;
    if (pc + imm >= n) return fin(9);
    steps++;
    if (sp < pops) return fin(2);
    if (sp - pops + pushes > 256) return fin(3);
    const next = pc + 1 + imm;
    pc = next;

    switch (op) {
      case 0x00:
        return fin(0);
      case 0x01: // PUSH8, sign-extended
        stack[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        stack[sp] = stack[sp - 1];
        sp++;
        break;
      case 0x05: {
        const x = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = x;
        break;
      }
      case 0x06:
        stack[sp] = stack[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = a;
        break;
      }
      case 0x17:
        stack[sp - 1] = (-stack[sp - 1]) | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x30:
      case 0x31:
      case 0x32: { // signed offset from the next instruction
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned absolute address
        if (csp >= 64) return fin(7);
        calls[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return fin(8);
        pc = calls[--csp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= 256) return fin(6);
        mem[addr] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // a PRINT past the output limit writes nothing
        const text = String(stack[sp - 1]);
        if (blen + text.length > 65_536) return fin(11);
        sp--;
        for (let i = 0; i < text.length; i++) buf[blen++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (blen + 1 > 65_536) return fin(11);
        buf[blen++] = stack[--sp] & 255;
        break;
      case 0x52: // IN: -1 once the input is used up
        stack[sp++] = ipos < input.length ? input[ipos++] : -1;
        break;
      case 0x53: // EXIT: the low byte of the value
        return fin(stack[--sp] & 255);
      default: { // binary operators: b is the top, a below it
        const b = stack[sp - 1];
        const a = stack[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return fin(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; // INT_MIN / -1 wraps to INT_MIN
            break;
          case 0x14:
            if (b === 0) return fin(4);
            r = b === -1 ? 0 : (a % b) | 0; // sign of the dividend; x % -1 is 0
            break;
          case 0x15:
            if (b === 0) return fin(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // DIVU: operands read unsigned
            break;
          case 0x16:
            if (b === 0) return fin(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // shift counts are mod 32
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU: unsigned
          default: return fin(5); // unreachable: the table gates this
        }
        sp -= 2;
        stack[sp++] = r;
        break;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
