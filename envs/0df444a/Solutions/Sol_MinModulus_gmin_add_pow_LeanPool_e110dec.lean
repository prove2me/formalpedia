-- Prove2me | solution 1 for MinModulus.gmin_add_pow_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:30.750093+00:00
-- url     : https://prove2.me/submissions/ef1c9605-edb9-401e-a3f2-05dd405392db

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
theorem _root_.solution : ∀ w X, gmin w (X + 2 ^ w) = gmin w X + 1 := by
  intro w
  induction w with
  | zero => intro X; simp [gmin]
  | succ w ih =>
    intro X
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    simp only [gmin]
    have e1 : (X + 2 ^ (w + 1)) % 2 = X % 2 := by omega
    have e2 : (X + 2 ^ (w + 1)) / 2 = X / 2 + 2 ^ w := by omega
    rw [e1, e2, ih (X / 2)]
    omega
end MinModulus
