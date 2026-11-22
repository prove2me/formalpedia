-- Prove2me | solution 1 for LongGapsBetweenPrimes.replacedResidueWeight_second_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:26.344902+00:00
-- url     : https://prove2.me/submissions/acb5b744-3f93-4ffe-bb59-9706cb184e70

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleProduct_dvd
import Theorems.Thm_LongGapsBetweenPrimes_weightedResidueWeight_second_moment_le
import Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_eq_weighted
import Theorems.Thm_LongGapsBetweenPrimes_weighted_diagonal_le
import Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_square_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 1 < M) (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ))
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (hroot : ∀ p, Function.Injective (root p))
    (i : Fin (k + 1)) :
    Finset.expect Finset.univ (fun t => replacedResidueWeight P (k + 1) D root i t ^ 2) ≤
      Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) * coefficientMoment P (2 * β) ^ k +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by
  classical
  simp_rw [replacedResidueWeight_eq_weighted h.squarefree]
  apply (weightedResidueWeight_second_moment_le h.squarefree hM hmin
    (fun p j => root p (i.succAbove j))
    (fun p a b hab => by simpa using hroot p hab)
    (fun r => coefficientRemainder P (tupleProduct r) D)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply weighted_diagonal_le (by positivity) (by positivity)
  intro r hr
  obtain ⟨hpair, hcut⟩ := (Finset.mem_filter.mp hr).2
  exact coefficientRemainder_square_le h hβ (tupleProduct_dvd r hpair) hcut
    (zero_lt_one.trans hM) hmin
end LongGapsBetweenPrimes
