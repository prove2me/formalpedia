-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientRemainder_square_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:10:52.220957+00:00
-- url     : https://prove2.me/submissions/ece71475-09ae-4b01-ae59-96324422262d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_nonneg
import Theorems.Thm_LongGapsBetweenPrimes_coefficientRemainder_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P m : ℕ} {β C D M : ℝ}
    (h : CoefficientEstimates P β C) (hβ : 0 ≤ β) (hm : m ∣ P)
    (hcut : (m : ℝ) ≤ D) (hM : 0 < M)
    (hmin : ∀ p ∈ P.primeFactors, M ≤ (p : ℝ)) :
    coefficientRemainder P m D ^ 2 ≤
      (2 * C ^ 2 * D ^ (-(2 * β))) * (m : ℝ) ^ (2 * β) +
        2 * (4 * Real.log D / (M * Real.log 2)) ^ 2 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero h.squarefree.ne_zero hm)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hD : 0 < D := hm'.trans_le hcut
  have hs := pow_le_pow_left₀ (coefficientRemainder_nonneg h.one_lt hm0 hcut)
    (coefficientRemainder_le h hβ hm hcut hM hmin) 2
  have hp : (((m : ℝ) / D) ^ β) ^ 2 = D ^ (-(2 * β)) * (m : ℝ) ^ (2 * β) := by
    rw [← Real.rpow_mul_natCast (div_nonneg hm'.le hD.le), Real.rpow_neg hD.le,
      Real.div_rpow hm'.le hD.le]
    norm_num
    rw [mul_comm β 2]
    ring
  have hsq := sq_nonneg (C * ((m : ℝ) / D) ^ β - 4 * Real.log D / (M * Real.log 2))
  nlinarith [hp]
end LongGapsBetweenPrimes
