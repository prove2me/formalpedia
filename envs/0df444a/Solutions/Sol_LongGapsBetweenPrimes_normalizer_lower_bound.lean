-- Prove2me | solution 1 for LongGapsBetweenPrimes.normalizer_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:04.276497+00:00
-- url     : https://prove2.me/submissions/4b778673-48f9-48d4-8723-b1e3bce37036

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_lower_integral

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) {A : ℝ}
    (hA : 0 < A) (hZA : eulerProduct Z 1 ≤ A)
    (hAY : A ≤ Real.log ((Y : ℝ) + 1)) :
    Real.log (Real.log ((Y : ℝ) + 1)) - Real.log A - 2 ≤
      2 * A * normalizer (auxiliaryProduct Z Y) := by
  have hlog : 0 < Real.log ((Y : ℝ) + 1) := hA.trans_le hAY
  have h := normalizer_lower_integral hZY hA (one_div_pos.mpr hlog)
    (one_div_le_one_div_of_le hA hAY) hZA
    (by rw [one_div_mul_cancel hlog.ne'])
  simp only [one_div, Real.log_inv] at h
  have hmul := (div_le_iff₀ (show 0 < 2 * A by positivity)).mp
    (sub_le_iff_le_add.mp h)
  nlinarith [mul_inv_cancel₀ hA.ne',
    mul_nonneg hA.le (inv_nonneg.mpr hlog.le)]
end LongGapsBetweenPrimes
