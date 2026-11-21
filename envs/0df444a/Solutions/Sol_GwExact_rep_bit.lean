-- Prove2me | solution 1 for GwExact.rep_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:48.041344+00:00
-- url     : https://prove2.me/submissions/aaf079b5-1d0d-4698-ae05-495f7efd3494

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
theorem _root_.solution (R : Nat) : ∀ i j, j < i → (rep R i).testBit (j * R) = true := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj
    show (Nat.lor (rep R i) (bit (i * R))).testBit _ = true
    rw [testBit_lor', Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact Or.inl (ih j hj)
    · right; rw [testBit_bit]; subst hj; simp
end GwExact
