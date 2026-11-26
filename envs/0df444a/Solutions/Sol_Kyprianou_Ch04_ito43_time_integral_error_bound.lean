-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_time_integral_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:14:51.688557+00:00
-- url     : https://prove2.me/submissions/d1b6b48f-2c48-453b-89f8-c6a645447f00

import Mathlib
open MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

/-- An error integral over a variable subinterval is bounded by the full L1 error. -/
theorem solution (a b : ℝ → ℝ) (T t : ℝ) (ht : t ≤ T)
    (ha : IntegrableOn a (Icc 0 T)) (hb : IntegrableOn b (Icc 0 T)) :
    |(∫ s in Icc 0 t, a s) - ∫ s in Icc 0 t, b s| ≤
      ∫ s in Icc 0 T, |a s - b s| := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht
  have ha' := ha.mono_set hsub
  have hb' := hb.mono_set hsub
  rw [← integral_sub ha' hb']
  calc
    _ ≤ ∫ s in Icc 0 t, |a s - b s| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Icc 0 t)) (fun s => a s - b s)
    _ ≤ _ := setIntegral_mono_set (ha.sub hb).abs
      (ae_of_all _ fun s => abs_nonneg _) hsub.eventuallyLE
