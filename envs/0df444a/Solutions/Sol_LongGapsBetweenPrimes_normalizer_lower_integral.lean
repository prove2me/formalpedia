-- Prove2me | solution 1 for LongGapsBetweenPrimes.normalizer_lower_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:55.204124+00:00
-- url     : https://prove2.me/submissions/17cd2467-aa9f-453d-944a-cf9e2a86b9f6

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryProduct_pos
import Theorems.Thm_LongGapsBetweenPrimes_divisorEulerMoment_lower
import Theorems.Thm_LongGapsBetweenPrimes_continuous_divisorEulerMoment
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_integral_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {Z Y : ℕ} (hZY : Z ≤ Y) {A a b : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hab : a ≤ b) (hZA : eulerProduct Z 1 ≤ A)
    (hscale : 1 ≤ a * Real.log ((Y : ℝ) + 1)) :
    (Real.log b - Real.log a) / (2 * A) - (b - a) ≤ normalizer (auxiliaryProduct Z Y) := by
  have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
    rw [Set.uIcc_of_le hab]
    exact fun t ht => ha.trans_le ht.1
  have hinv : IntervalIntegrable (fun t : ℝ => 1 / t) MeasureTheory.volume a b :=
    (continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')).intervalIntegrable
  calc
    _ = ∫ t : ℝ in a..b, (1 / t) / (2 * A) - 1 := by
      rw [intervalIntegral.integral_sub (hinv.div_const _) intervalIntegrable_const,
        intervalIntegral.integral_div, integral_one_div (by
          intro ht
          exact (hpos 0 ht).false),
        Real.log_div (ha.trans_le hab).ne' ha.ne']
      simp
    _ ≤ ∫ t : ℝ in a..b, divisorEulerMoment (auxiliaryProduct Z Y) (-t) - 1 := by
      apply intervalIntegral.integral_mono_on hab
        ((hinv.div_const _).sub intervalIntegrable_const)
        (((continuous_divisorEulerMoment _).sub continuous_const).intervalIntegrable a b)
      intro t ht
      have htpos := ha.trans_le ht.1
      have htscale : 1 ≤ t * Real.log ((Y : ℝ) + 1) :=
        hscale.trans (mul_le_mul_of_nonneg_right ht.1
          (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg Y))))
      calc
        (1 / t) / (2 * A) - 1 = 1 / (2 * t * A) - 1 := by ring
        _ ≤ _ := sub_le_sub_right (divisorEulerMoment_lower hZY htpos hA hZA htscale) 1
    _ ≤ normalizer (auxiliaryProduct Z Y) :=
      normalizer_integral_le (auxiliaryProduct_pos Z Y).ne' ha.le b
end LongGapsBetweenPrimes
