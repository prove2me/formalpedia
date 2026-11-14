-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_finite_intensity
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:25:57.076205+00:00
-- url     : https://prove2.me/submissions/040a9faa-316b-4cc4-8862-d26567202be9

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_intensity_bound
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (ν : Measure ℝ)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞) :
    (ν.withDensity fun z => ENNReal.ofReal (wInt z)) Set.univ ≠ ∞ := by
  apply lt_top_iff_ne_top.mp
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ z, ENNReal.ofReal (wInt z) ∂ν) ≤
        ∫⁻ z, (2:ℝ≥0∞)*ENNReal.ofReal (Real.cosh z) ∂ν := by
      apply lintegral_mono
      intro z
      have hh := ENNReal.ofReal_le_ofReal (soft_field_intensity_bound z)
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat] using hh
    _ = (2:ℝ≥0∞)*(∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) := lintegral_const_mul' 2 _ (by simp)
    _ < ∞ := ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hu)
