-- Prove2me | solution 1 for LongGapsBetweenPrimes.eulerProduct_ge_one_div_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:28.090871+00:00
-- url     : https://prove2.me/submissions/22b9731d-0cb5-4421-87db-fd1ed68f012f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_ge_power_integral

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (Y : ℕ) {t : ℝ} (ht : 0 < t)
    (hscale : 1 ≤ t * Real.log ((Y : ℝ) + 1)) :
    1 / (2 * t) ≤ eulerProduct Y (1 + t) := by
  have hpow : ((Y : ℝ) + 1) ^ (-t) ≤ 1 / 2 := by
    rw [Real.rpow_def_of_pos (by positivity),
      show Real.log ((Y : ℝ) + 1) * -t = -(t * Real.log ((Y : ℝ) + 1)) by ring,
      Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith [Real.add_one_le_exp (t * Real.log ((Y : ℝ) + 1))])
  calc
    1 / (2 * t) = (1 / 2) / t := by ring
    _ ≤ (1 - ((Y : ℝ) + 1) ^ (-t)) / t :=
      div_le_div_of_nonneg_right (by linarith) ht.le
    _ ≤ eulerProduct Y (1 + t) := eulerProduct_ge_power_integral Y ht
end LongGapsBetweenPrimes
