// Tiny stack VM, make.fun ISA v1. Reads each /input/<id>/{program,input}.bin,
// writes /output/<id>/{stdout.bin,exit.txt}. Node 22, no deps, deterministic.
import * as fs from "node:fs";
import * as path from "node:path";
const SM = 256, CM = 64, MW = 256, SL = 1000000, OM = 65536;
// In the grader the mounts come through MAKEFUN_INPUT_DIR /
// MAKEFUN_OUTPUT_DIR (on the server those are /input and /output).
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
// 255 in IM marks a byte no opcode names.
const IM = new Uint8Array(256).fill(255), PO = new Uint8Array(256), PU = new Uint8Array(256);
for (const [o, i, p, q] of [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]]) { IM[o] = i; PO[o] = p; PU[o] = q; }

function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length, st = new Int32Array(SM);
  let sp = 0;
  const cs = new Int32Array(CM);
  let cp = 0;
  const mm = new Int32Array(MW), ob = new Uint8Array(OM);
  let ol = 0, ip = 0, pc = 0, stp = 0;
  const fin = (e: number): [Uint8Array, number] => [ob.subarray(0, ol), e];
  for (;;) {
    if (stp === SL) return fin(10); // step limit
    if (pc < 0 || pc >= n) return fin(9); // pc outside the program
    const op = p[pc], im = IM[op];
    if (im === 255) return fin(5); // unknown opcode
    if (pc + im >= n) return fin(9); // immediate cut off
    stp++;
    const nx = pc + 1 + im, pops = PO[op], pushes = PU[op];
    if (sp < pops) return fin(2); // stack underflow
    if (sp - pops + pushes > SM) return fin(3); // stack overflow
    pc = nx;
    switch (op) {
      case 0: return fin(0); // HALT
      case 1: st[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: st[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break; // PUSH32, little-endian
      case 3: sp--; break; // POP
      case 4: st[sp] = st[sp - 1]; sp++; break; // DUP
      case 5: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
      case 6: st[sp] = st[sp - 2]; sp++; break; // OVER
      case 7: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; } // ROT
      case 23: st[sp - 1] = -st[sp - 1] | 0; break; // NEG, wraps
      case 27: st[sp - 1] = ~st[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = st[sp - 1], a = st[sp - 2]; // b is the top
        let r: number;
        switch (op) {
          case 16: r = (a + b) | 0; break; // ADD, wraps
          case 17: r = (a - b) | 0; break; // SUB, wraps
          case 18: r = Math.imul(a, b); break; // MUL, low 32 bits
          case 19: // DIV, truncated toward zero
            if (b === 0) return fin(4);
            r = a === -2147483648 && b === -1 ? -2147483648 : (a / b) | 0;
            break;
          case 20: // MOD, sign of a
            if (b === 0) return fin(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21: // DIVU, unsigned
            if (b === 0) return fin(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22: // MODU, unsigned
            if (b === 0) return fin(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break; // AND
          case 25: r = a | b; break; // OR
          case 26: r = a ^ b; break; // XOR
          case 28: r = a << (b & 31); break; // SHL
          case 29: r = a >> (b & 31); break; // SHR, arithmetic
          case 30: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 32: r = a === b ? 1 : 0; break; // EQ
          case 33: r = a < b ? 1 : 0; break; // LT, signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU, unsigned
        }
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 48: case 49: case 50: { // JMP / JZ / JNZ, offset signed 16-bit from next
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) {
          const v = st[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL: push next address, jump to unsigned 16-bit target
        if (cp === CM) return fin(7);
        cs[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return fin(8);
        pc = cs[--cp];
        break;
      case 64: { // LOAD
        const ad = st[sp - 1];
        if (ad < 0 || ad >= MW) return fin(6);
        st[sp - 1] = mm[ad];
        break;
      }
      case 65: { // STORE: (v addr --), addr is the top
        const ad = st[sp - 1], v = st[sp - 2];
        if (ad < 0 || ad >= MW) return fin(6);
        sp -= 2;
        mm[ad] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline
        const s = String(st[sp - 1]);
        if (ol + s.length > OM) return fin(11);
        sp--;
        for (let i = 0; i < s.length; i++) ob[ol++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, low 8 bits
        if (ol + 1 > OM) return fin(11);
        ob[ol++] = st[--sp] & 255;
        break;
      case 82: // IN: next input byte, -1 once used up
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83: // EXIT: low byte of the popped value
        return fin(st[--sp] & 255);
      default:
        return fin(5); // unreachable: unknown opcodes trap above
    }
  }
}

function main(): void {
  let ids: string[];
  try {
    ids = fs.readdirSync(IN_DIR).filter((d) => /^i\d{3}$/.test(d)).sort();
  } catch {
    ids = [];
  }
  if (ids.length === 0) {
    ids = [];
    for (let k = 1; k <= 40; k++) ids.push("i" + String(k).padStart(3, "0"));
  }
  for (const id of ids) {
    const dir = path.join(OUT_DIR, id);
    try {
      const [out, exit] = run(
        fs.readFileSync(path.join(IN_DIR, id, "program.bin")),
        fs.readFileSync(path.join(IN_DIR, id, "input.bin")),
      );
      fs.mkdirSync(dir, { recursive: true });
      fs.writeFileSync(path.join(dir, "stdout.bin"), out);
      fs.writeFileSync(path.join(dir, "exit.txt"), String(exit));
    } catch {
      try {
        fs.mkdirSync(dir, { recursive: true });
        fs.writeFileSync(path.join(dir, "stdout.bin"), Buffer.alloc(0));
        fs.writeFileSync(path.join(dir, "exit.txt"), "9");
      } catch { /* ignore */ }
    }
  }
}

main();
