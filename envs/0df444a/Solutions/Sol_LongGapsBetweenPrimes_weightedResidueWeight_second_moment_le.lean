-- Prove2me | solution 1 for LongGapsBetweenPrimes.weightedResidueWeight_second_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:03.421164+00:00
-- url     : https://prove2.me/submissions/0c2e16e2-33ae-455d-afb8-599e6788c2c9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_indexed_product_second_moment
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_injective
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_tupleAssignment
import Theorems.Thm_LongGapsBetweenPrimes_assignmentNormalizer_mul_basis
import Theorems.Thm_LongGapsBetweenPrimes_tupleNormalizedCoefficient_sq
import Theorems.Thm_LongGapsBetweenPrimes_assignment_row_bound_all

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P)
    {D M : ℝ} (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (b : DivisorTuple P k → ℝ) :
    Finset.expect Finset.univ (fun t => weightedResidueWeight P k D root b t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by
  classical
  have hsize (p : PrimeIndex P) : 1 < p.val :=
    (Nat.prime_of_mem_primeFactors p.property).one_lt
  have hmass :
      (∑ r : tupleRegion P k D, (b r.val * tupleNormalizedCoefficient r.val) ^ 2) =
        ∑ r ∈ tupleRegion P k D, tupleMass r * b r ^ 2 := by
    rw [← Finset.sum_attach (tupleRegion P k D) (fun r => tupleMass r * b r ^ 2)]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_pow, tupleNormalizedCoefficient_sq hP r.val
      (Finset.mem_filter.mp r.property).2.1, mul_comm]
  have hweight (t : (p : PrimeIndex P) → Fin p.val) :
      (∑ r : tupleRegion P k D, (b r.val * tupleNormalizedCoefficient r.val) *
        productBasis (fun p => localBasis (root p)) (tupleAssignment r.val) t) =
      weightedResidueWeight P k D root b t := by
    simp only [tupleNormalizedCoefficient, mul_assoc,
      assignmentNormalizer_mul_basis _ hsize, weightedResidueWeight]
  have hbound (r : tupleRegion P k D) :
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤
        Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) - 1 := by
    apply sub_le_sub_right _ 1
    apply assignment_row_bound_all (fun p : PrimeIndex P => p.val)
      (tupleAssignment r.val) hM (fun p => hmin p.val p.property)
    rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
    exact (Finset.mem_filter.mp r.property).2.2
  have h := indexed_product_second_moment (fun p : PrimeIndex P => p.val) hsize root hroot
    (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D)
    (fun r => b r.val * tupleNormalizedCoefficient r.val) _ hbound
  simp only [hweight, hmass] at h
  linarith [(abs_le.mp h).2]
end LongGapsBetweenPrimes
