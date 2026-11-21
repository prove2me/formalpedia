-- Prove2me | solution 1 for MinModulus.unshift_dsum_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:30.198233+00:00
-- url     : https://prove2.me/submissions/b1fa165e-ded0-424c-be1f-8eceb6911d2e

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
    dsum (w + 1) k = k 0 + dsum w (fun i => k (i + 1)) := by
  have h := shift_dsum w (k 0) (fun i => k (i + 1))
  have hk : dsum (w + 1) (shift (k 0) (fun i => k (i + 1))) = dsum (w + 1) k := by
    unfold dsum
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [shift]
    · have hne : i ≠ 0 := by omega
      have hi1 : i - 1 + 1 = i := by omega
      simp only [shift, if_neg hne, hi1]
  rw [hk] at h
  omega
end MinModulus
