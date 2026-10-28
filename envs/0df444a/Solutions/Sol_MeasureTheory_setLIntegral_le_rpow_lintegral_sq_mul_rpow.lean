-- Prove2me | solution 1 for MeasureTheory.setLIntegral_le_rpow_lintegral_sq_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:54:30.414833+00:00
-- url     : https://prove2.me/submissions/a390eba4-1921-4c8a-9fc0-76ed3c7e3076

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open scoped ENNReal NNReal
open MeasureTheory
variable {Omega : Type*} [MeasurableSpace Omega]
theorem solution (mu : Measure Omega) {Z : Omega → ℝ≥0∞}
    (hZ : AEMeasurable Z mu) {A : Set Omega} (hA : MeasurableSet A) :
    ∫⁻ omega in A, Z omega ∂mu ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu A) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hg : AEMeasurable (A.indicator (fun _ => (1 : ℝ≥0∞))) mu :=
    (aemeasurable_const.indicator hA)
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq hZ hg
  have e1 : ∫⁻ omega in A, Z omega ∂mu = ∫⁻ omega, (Z * A.indicator (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
    rw [← lintegral_indicator hA]
    congr 1; ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have e2 : ∫⁻ omega, A.indicator (fun _ => (1 : ℝ≥0∞)) omega ^ (2 : ℝ) ∂mu = mu A := by
    rw [← lintegral_indicator_one hA]
    congr 1; ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have e3 : ∫⁻ omega, Z omega ^ (2 : ℝ) ∂mu = ∫⁻ omega, Z omega ^ 2 ∂mu := by
    congr 1; ext x; exact ENNReal.rpow_two (Z x)
  rw [e1]
  calc _ ≤ _ := h
    _ = _ := by rw [e2, e3]
