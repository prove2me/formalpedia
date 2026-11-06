-- Prove2me | solution 1 for Monodromy.Counter.TuringCompiler.encode_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:21:59.227378+00:00
-- url     : https://prove2.me/submissions/a91a550e-ed21-41a1-8541-fc3b1c5cf622

import Definitions.Def_Monodromy_Counter

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.TuringCompiler
open Turing

namespace Monodromy.TapeCode

variable {a : ℕ} [NeZero a]

@[simp] theorem encode_mk (word : List (Fin a)) :
    encode (ListBlank.mk word) = Nat.ofDigits (a + 1) (word.map Fin.val) := rfl

theorem encode_cons (symbol : Fin a) (tape : ListBlank (Fin a)) :
    encode (tape.cons symbol) = symbol.val + (a + 1) * encode tape := by
  refine ListBlank.induction_on tape (fun word => ?_)
  simp only [ListBlank.cons_mk, encode_mk, List.map_cons, Nat.ofDigits_cons]

theorem decomposition (tape : ListBlank (Fin a)) :
    encode tape = tape.head.val + (a + 1) * encode tape.tail := by
  simpa only [ListBlank.cons_head_tail] using encode_cons tape.head tape.tail

theorem head_code (tape : ListBlank (Fin a)) :
    encode tape % (a + 1) = tape.head.val := by
  rw [decomposition, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt)]

theorem tail_code (tape : ListBlank (Fin a)) :
    encode tape / (a + 1) = encode tape.tail := by
  rw [decomposition, Nat.add_mul_div_left _ _ (Nat.succ_pos a),
    Nat.div_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt), zero_add]

theorem nth_eq_of_code_eq (index : ℕ) (first second : ListBlank (Fin a))
    (same : encode first = encode second) : first.nth index = second.nth index := by
  induction index generalizing first second with
  | zero =>
      simp only [ListBlank.nth_zero]
      apply Fin.ext
      rw [← head_code first, ← head_code second, same]
  | succ index recursive =>
      rw [ListBlank.nth_succ, ListBlank.nth_succ]
      apply recursive
      rw [← tail_code first, ← tail_code second, same]

theorem encode_injective : Function.Injective (@encode a _) := by
  intro first second same
  apply ListBlank.ext
  intro index
  exact nth_eq_of_code_eq index first second same

end Monodromy.TapeCode

namespace Monodromy.Counter.TuringCompiler

variable (a q : ℕ) [NeZero a] [NeZero q]

omit [NeZero a] [NeZero q] in
theorem dispatch_injective : Function.Injective (dispatch a q) := by
  intro first second same
  exact congrArg Prod.fst ((address a q).injective same)

end Monodromy.Counter.TuringCompiler

variable (a q : ℕ) [NeZero a] [NeZero q]
omit [NeZero q]

theorem solution : Function.Injective (encode a q) := by
  intro first second same
  cases first with
  | mk fq ft =>
    cases second with
    | mk sq st =>
      cases ft with
      | mk fh fl fr =>
        cases st with
        | mk sh sl sr =>
          have row := dispatch_injective a q (congrArg Configuration.pc same)
          have left : TapeCode.encode fl = TapeCode.encode sl :=
            congrFun (congrArg Configuration.counters same) 0
          have right : TapeCode.encode fr = TapeCode.encode sr :=
            congrFun (congrArg Configuration.counters same) 1
          have heq : fh = sh := congrArg Prod.snd row
          have qeq : fq = sq := congrArg Prod.fst row
          have leq := TapeCode.encode_injective left
          have req := TapeCode.encode_injective right
          cases heq
          cases qeq
          cases leq
          cases req
          rfl
