-- Prove2me | solution 1 for LongGapsBetweenPrimes.residueWeight_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:44.219792+00:00
-- url     : https://prove2.me/submissions/93eb51d9-59fe-4de2-b48b-fe0059dd8b53

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_indexed_product_second_moment
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_injective
import Theorems.Thm_LongGapsBetweenPrimes_assignmentNormalizer_mul_basis
import Theorems.Thm_LongGapsBetweenPrimes_tupleNormalizedCoefficient_sq

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (ε : ℝ) (hbound : ∀ r : tupleRegion P k D,
      (∏ p : PrimeIndex P, localRow p.val k (tupleAssignment r.val p)) - 1 ≤ ε) :
    |Finset.expect Finset.univ (fun t => residueWeight P k D root t ^ 2) - diagonalMass P k D| ≤
      ε * diagonalMass P k D := by
  classical
  have hsize (p : PrimeIndex P) : 1 < p.val :=
    (Nat.prime_of_mem_primeFactors p.property).one_lt
  have hmass : (∑ r : tupleRegion P k D, tupleNormalizedCoefficient r.val ^ 2) =
      diagonalMass P k D := by
    rw [diagonalMass, ← Finset.sum_attach (tupleRegion P k D) tupleMass]
    apply Finset.sum_congr rfl
    intro r _
    exact tupleNormalizedCoefficient_sq hP r.val (Finset.mem_filter.mp r.property).2.1
  have hweight (t : (p : PrimeIndex P) → Fin p.val) :
      (∑ r : tupleRegion P k D, tupleNormalizedCoefficient r.val *
        productBasis (fun p => localBasis (root p)) (tupleAssignment r.val) t) =
      residueWeight P k D root t := by
    simp only [tupleNormalizedCoefficient, mul_assoc,
      assignmentNormalizer_mul_basis _ hsize, residueWeight]
  simpa only [hweight, hmass] using
    indexed_product_second_moment (fun p : PrimeIndex P => p.val) hsize root hroot
      (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D)
      (fun r => tupleNormalizedCoefficient r.val) ε hbound
end LongGapsBetweenPrimes
