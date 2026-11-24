-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_primitive_exp_product_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:33:08.280042+00:00
-- url     : https://prove2.me/submissions/18451df5-f987-45b9-b68d-97f8e3680aa8

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option autoImplicit false
open MeasureTheory Set
/-- Integrate the product derivative. -/
theorem solution :
    ∀ (φ : ℝ) (v : ℝ → ℝ), Continuous v → ∀ b : ℝ,
      (∫ t in (0 : ℝ)..b, Real.exp (-φ*t) *
        (v t - φ * (∫ s in (0 : ℝ)..t, v s))) =
      Real.exp (-φ*b) * (∫ s in (0 : ℝ)..b, v s) := by
  intro φ v hv b
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, v s
  have hD (t : ℝ) : HasDerivAt H (v t) t :=
    intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
      hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun t => (hD t).continuousAt
  have hG (t : ℝ) : HasDerivAt (fun s => Real.exp (-φ * s) * H s)
      (Real.exp (-φ * t) * (v t - φ * H t)) t := by
    have hd := (((hasDerivAt_id t).const_mul (-φ)).exp).mul (hD t)
    convert hd using 1 <;> (try simp only [id_eq]) <;> first | rfl | ring
  have hc : Continuous (fun t => Real.exp (-φ * t) * (v t - φ * H t)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hv.sub (continuous_const.mul hH))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := b) (fun t _ => hG t) (hc.intervalIntegrable 0 b)
  simpa [H] using hi
