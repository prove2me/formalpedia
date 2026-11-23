-- Prove2me | solution 1 for GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:32.914168+00:00
-- url     : https://prove2.me/submissions/f6cbc4ed-0859-47e6-aed5-7bf529b7cb38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqSumEqSumSqAddTwoMulSumLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
open Matrix Finset Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by
  have h : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if k < i then j k * j i else 0) + (if i = k then j i ^ 2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne, not_lt.mpr hik.le]
    · subst hik; simp [sq]
    · simp [hik, hik.ne', not_lt.mpr hik.le, mul_comm]
  calc (∑ i, j i) ^ 2 = ∑ i, ∑ k, j i * j k := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ((if i < k then j i * j k else 0) + (if k < i then j k * j i else 0) +
          (if i = k then j i ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h i k
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
end _root_.GlobalTheory
end GlobalTheory
