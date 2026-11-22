-- Prove2me | solution 1 for LongGapsBetweenPrimes.diagonalMass_normalized_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:41.144937+00:00
-- url     : https://prove2.me/submissions/e42508d9-860b-4355-a556-ac778dc2a0ef

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_pow_le
import Theorems.Thm_LongGapsBetweenPrimes_diagonalMass_tail_collision
import Theorems.Thm_LongGapsBetweenPrimes_CoefficientEstimates_one_le_constant

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P M k : ℕ} {β C D : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hD : 0 < D)
    (hM : 0 < M) (hmin : ∀ p ∈ P.primeFactors, M < p) :
    (1 - (D ^ (-β) * Real.exp ((k : ℝ) * C * β) + 16 * (k : ℝ) ^ 2 / M)) *
      coefficientMoment P 0 ^ k ≤ diagonalMass P k D := by
  have hmoment := coefficientMoment_pow_le h.one_lt
    (zero_le_one.trans (h.one_le_constant hβ)) hβ
    (h.moment_control β hβ (by linarith)) k
  have hloss := diagonalMass_tail_collision (k := k) h hM hmin hD hβ
  have htail := mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg hD.le (-β))
  nlinarith
end LongGapsBetweenPrimes
