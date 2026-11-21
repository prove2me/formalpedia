-- Prove2me | solution 1 for MinModulus.gmin_ones_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:19.678626+00:00
-- url     : https://prove2.me/submissions/680d0c00-e0c0-4314-a6d1-21bae1d97761

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
theorem _root_.solution : ∀ w, gmin w (2 ^ (w + 1) - 1) = w + 1 := by
  intro w
  induction w with
  | zero => norm_num [gmin]
  | succ w ih =>
    have h2 : 2 ^ (w + 1 + 1) = 2 * 2 ^ (w + 1) := by rw [pow_succ]; ring
    have h1 : 1 ≤ 2 ^ (w + 1) := Nat.one_le_pow _ _ (by norm_num)
    simp only [gmin]
    have e1 : (2 ^ (w + 1 + 1) - 1) % 2 = 1 := by omega
    have e2 : (2 ^ (w + 1 + 1) - 1) / 2 = 2 ^ (w + 1) - 1 := by omega
    rw [e1, e2, ih]
    omega
end MinModulus
