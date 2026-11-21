-- Prove2me | solution 1 for MinModulus.unshift_val_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:20.359245+00:00
-- url     : https://prove2.me/submissions/3bfe881d-189f-4e61-8ffe-a65cae6de476

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
theorem _root_.solution (w : ℕ) (k : ℕ → ℕ) :
    val (w + 1) k = k 0 + 2 * val w (fun i => k (i + 1)) := by
  have h := shift_val w (k 0) (fun i => k (i + 1))
  have hk : val (w + 1) (shift (k 0) (fun i => k (i + 1))) = val (w + 1) k := by
    unfold val
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [shift]
    · have hne : i ≠ 0 := by omega
      have hi1 : i - 1 + 1 = i := by omega
      simp only [shift, if_neg hne, hi1]
  rw [hk] at h
  omega
end MinModulus
