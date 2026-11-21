-- Prove2me | solution 1 for MasulloGRH.positiveHaar_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:17:58.531176+00:00
-- url     : https://prove2.me/submissions/5c660057-353d-4ab8-941e-d8b28d08cf80

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

theorem solution :
    Measure.map Real.exp (volume : Measure ℝ) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal t⁻¹) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg Real.measurable_exp,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := univ) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy)
    (fun t => ENNReal.ofReal t⁻¹ * g t)
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h
  simp only [Pi.mul_apply]
  rw [h]
  apply lintegral_congr
  intro x
  rw [abs_of_pos (Real.exp_pos x), ← mul_assoc, ← ENNReal.ofReal_mul
    (le_of_lt (Real.exp_pos x)), mul_inv_cancel₀ (Real.exp_ne_zero x)]
  simp
