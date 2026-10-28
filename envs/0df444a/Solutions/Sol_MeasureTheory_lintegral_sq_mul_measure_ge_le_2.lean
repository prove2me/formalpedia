-- Prove2me | solution 2 for MeasureTheory.lintegral_sq_mul_measure_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:07:28.853969+00:00
-- url     : https://prove2.me/submissions/8e52eef3-82aa-4e63-8007-a176c20b7063

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open scoped ENNReal NNReal
open MeasureTheory
variable {Omega : Type*} [MeasurableSpace Omega]
theorem cs_aux (mu : Measure Omega) {Z : Omega → ℝ≥0∞}
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

theorem solution (mu : Measure Omega) [IsProbabilityMeasure mu]
    {Z : Omega → ℝ≥0∞} (hZ : Measurable Z) (hfin : ∫⁻ omega, Z omega ∂mu ≠ ⊤) (rho : ℝ≥0) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, Z omega ∂mu) ^ 2 ≤
      (∫⁻ omega, Z omega ^ 2 ∂mu) *
        mu {omega | (rho : ℝ≥0∞) * ∫⁻ omega, Z omega ∂mu ≤ Z omega} := by
  set E := ∫⁻ omega, Z omega ∂mu with hE
  set A := {omega | (rho : ℝ≥0∞) * E ≤ Z omega} with hA
  have hAm : MeasurableSet A := measurableSet_le measurable_const hZ
  have hsplit := lintegral_add_compl (μ := mu) Z hAm
  have hc : ∫⁻ omega in Aᶜ, Z omega ∂mu ≤ (rho : ℝ≥0∞) * E := by
    calc ∫⁻ omega in Aᶜ, Z omega ∂mu ≤ ∫⁻ omega in Aᶜ, (rho : ℝ≥0∞) * E ∂mu := by
          apply setLIntegral_mono measurable_const
          intro x hx
          simp only [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
          exact hx.le
      _ = (rho : ℝ≥0∞) * E * mu Aᶜ := setLIntegral_const _ _
      _ ≤ (rho : ℝ≥0∞) * E * 1 := by gcongr; exact prob_le_one
      _ = _ := mul_one _
  have h1 : E ≤ (rho : ℝ≥0∞) * E + ∫⁻ omega in A, Z omega ∂mu := by
    calc E = ∫⁻ omega in A, Z omega ∂mu + ∫⁻ omega in Aᶜ, Z omega ∂mu := hsplit.symm
      _ ≤ ∫⁻ omega in A, Z omega ∂mu + (rho : ℝ≥0∞) * E := by gcongr
      _ = _ := add_comm _ _
  have h2 : ((1 : ℝ≥0∞) - rho) * E ≤ ∫⁻ omega in A, Z omega ∂mu := by
    rw [ENNReal.sub_mul (fun _ _ => hfin), one_mul]
    exact tsub_le_iff_left.mpr h1
  have h3 := cs_aux mu hZ.aemeasurable hAm
  have sq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    intro a; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc ((1 : ℝ≥0∞) - rho) ^ 2 * E ^ 2 = (((1 : ℝ≥0∞) - rho) * E) ^ 2 := by ring
    _ ≤ ((∫⁻ omega, Z omega ^ 2 ∂mu) ^ (1 / 2 : ℝ) * (mu A) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (zero_le) (h2.trans h3) 2
    _ = _ := by rw [mul_pow, sq, sq]
