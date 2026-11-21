-- Prove2me | solution 1 for MinModulus.gmin_add_le_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:29.738426+00:00
-- url     : https://prove2.me/submissions/b91a4478-b737-4182-a584-8277bf37b8d1

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution : ∀ w x t, gmin w (x + t) ≤ gmin w x + t := by
  intro w
  induction w with
  | zero => intro x t; simp [gmin]
  | succ w ih =>
    intro x t
    simp only [gmin]
    obtain ⟨t', ht'⟩ : ∃ t', (x + t) / 2 = x / 2 + t' :=
      ⟨(x + t) / 2 - x / 2, by omega⟩
    have h2 := ih (x / 2) t'
    rw [ht']
    omega
end MinModulus
