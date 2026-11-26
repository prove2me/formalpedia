-- Prove2me | solution 1 for Kyprianou.Ch04.levyBandEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:52:50.440742+00:00
-- url     : https://prove2.me/submissions/91c1a52f-80ec-450c-9b16-fc7640dad395

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Quadratic energy of a finite small-jump band is integrable and bounded by a larger band. -/
theorem solution (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfin : ν B < ⊤) (hBC : B ⊆ C) (hC1 : ∀ z ∈ C, |z| ≤ 1) :
    Integrable (B.indicator (fun z : ℝ => z^2)) ν ∧
      0 ≤ (∫ z, B.indicator (fun z : ℝ => z^2) z ∂ν) ∧
      (∫ z, B.indicator (fun z : ℝ => z^2) z ∂ν) ≤
        (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν).toReal := by
  haveI : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hfin.ne
  have hi : Integrable (fun z : ℝ => z^2) (ν.restrict B) := by
    apply Integrable.of_bound (measurable_id.pow_const 2).aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem hB] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change z^2 ≤ 1
    have h := hC1 z (hBC hz)
    nlinarith [sq_abs z, abs_nonneg z]
  have hnn : 0 ≤ ∫ z in B, z^2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hCfin : (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν) < ⊤ := by
    have heq : (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν) =
        ∫⁻ z in C, ENNReal.ofReal (min 1 (z^2)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hC] with z hz
      rw [min_eq_right]
      nlinarith [hC1 z hz, sq_abs z, abs_nonneg z]
    rw [heq]
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hν.2
  have hb := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z => sq_nonneg z)
  have hle : (∫⁻ z in B, ENNReal.ofReal (z^2) ∂ν) ≤
      ∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν :=
    lintegral_mono' (Measure.restrict_mono hBC le_rfl) le_rfl
  rw [← hb] at hle
  refine ⟨(integrable_indicator_iff hB).2 hi, ?_, ?_⟩
  · rwa [integral_indicator hB]
  · rw [integral_indicator hB]
    simpa [ENNReal.toReal_ofReal hnn] using ENNReal.toReal_mono hCfin.ne hle
