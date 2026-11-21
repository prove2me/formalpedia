-- Prove2me | solution 1 for GwExact.monoMask_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:34.216176+00:00
-- url     : https://prove2.me/submissions/0c6f4e19-f210-4c23-8b79-ef7ff723d177

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
public import Theorems.Thm_GwExact_testBit_bit
public import Theorems.Thm_P2M_GwExact_testBit_lor__e8313c48450e

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (R c a d : Nat) : ∀ m j, j < m →
    (monoMask R c a d m).testBit ((a + j * d) * R + c) = true := by
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    show (Nat.lor (monoMask R c a d m) (bit ((a + m * d) * R + c))).testBit _ = true
    rw [testBit_lor', Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact Or.inl (ih j hj)
    · right; rw [testBit_bit]; subst hj; simp
end GwExact
