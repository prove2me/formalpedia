-- Prove2me | solution 1 for Kyprianou.Ch04.normalisedTailDensityIsProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:59:39.018615+00:00
-- url     : https://prove2.me/submissions/a90925df-47fc-44c0-95b9-5dd1824d85ef

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Inv
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
/-- Normalising a finite positive ENNReal density yields a probability measure. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ENNReal) (hf : Measurable f)
    (k : ENNReal) (hk : 0 < k) (hktop : k ≠ ⊤)
    (hmass : (∫⁻ x : α, f x ∂μ) = k) :
    IsProbabilityMeasure (μ.withDensity (fun x => f x / k)) := by
  rw [isProbabilityMeasure_iff]
  rw [withDensity_apply _ MeasurableSet.univ]
  have hlin :
      (∫⁻ x : α, f x / k ∂μ) = (∫⁻ x : α, f x ∂μ) * k⁻¹ := by
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const k⁻¹ hf
  simpa [hlin, hmass] using ENNReal.mul_inv_cancel (ne_of_gt hk) hktop
