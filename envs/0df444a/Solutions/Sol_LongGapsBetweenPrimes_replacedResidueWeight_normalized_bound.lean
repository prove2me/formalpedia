-- Prove2me | solution 1 for LongGapsBetweenPrimes.replacedResidueWeight_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:57.17133+00:00
-- url     : https://prove2.me/submissions/744aa879-a880-42d1-b6e4-bf18c7876fdc

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_pow_le
import Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_second_moment_le
import Theorems.Thm_LongGapsBetweenPrimes_CoefficientEstimates_one_le_constant

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
      uncoveredBound k β C M D * coefficientMoment P 0 ^ k := by
  have hγ : 0 ≤ 2 * β := mul_nonneg (by norm_num) hβ
  have hmoment := coefficientMoment_pow_le h.one_lt
    (zero_le_one.trans (h.one_le_constant hβ)) hγ
    (h.moment_control (2 * β) hγ le_rfl) k
  apply (replacedResidueWeight_second_moment_le h hβ hD hM hmin root hroot i).trans
  unfold uncoveredBound gramBound
  calc
    _ ≤ Real.exp ((k : ℝ) * Real.log D / ((M - 1) * Real.log M)) *
        ((2 * C ^ 2 * D ^ (-(2 * β))) *
            (coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * (2 * β))) +
          2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 * coefficientMoment P 0 ^ k) := by
      gcongr
    _ = _ := by ring
end LongGapsBetweenPrimes
