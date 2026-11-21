-- Prove2me | solution 1 for MinModulus.slack_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:51.92269+00:00
-- url     : https://prove2.me/submissions/03779116-ab37-476e-8203-86f9c163d24c

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
public import Theorems.Thm_MinModulus_gmin_ones_LeanPool_e110dec
public import Theorems.Thm_MinModulus_gmin_step_LeanPool_e110dec

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution {w t N : ℕ} (ht : t ≤ w) (hN : N + 2 ^ t = 2 ^ (w + 1)) :
    ∀ j, w + 1 + j ≤ gmin w (2 ^ (w + 1) - 1 + j * N) := by
  intro j
  induction j with
  | zero =>
    have h := gmin_ones_LeanPool_e110dec w
    simp only [Nat.zero_mul, Nat.add_zero]
    omega
  | succ j ih =>
    have hmul : (j + 1) * N = j * N + N := by ring
    have h1 : 1 ≤ 2 ^ (w + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hstep := gmin_step_LeanPool_e110dec w t (2 ^ (w + 1) - 1 + j * N)
      (2 ^ (w + 1) - 1 + (j + 1) * N) ht (by omega)
    omega
end MinModulus
