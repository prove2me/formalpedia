-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:24:56.167685+00:00
-- url     : https://prove2.me/submissions/43568474-5174-4b28-95c8-9f6a79359f5b

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- The compensated-Poisson integral is measurable at each time. -/
theorem LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ hm hp hs t ω :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN φ hm hp hs
    t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl
omit [IsProbabilityMeasure P] in
/-- The mark-indexed `L²` energy of a difference vanishing a.e. on the window is zero. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_sub_mark_eq_zero_of_ae {ν : Measure E} {t : ℝ} (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with s hs
  simp [hs]
/-- Integrands agreeing a.e. on `[0, t]` have a.e. equal compensated-Poisson integrals at `t`. -/
theorem solution {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), φ₁ ω s = φ₂ ω s) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω := by
  have hiso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
    N ℱ hℱN φ₁ φ₂ hm₁ hm₂ hp₁ hp₂ hs₁ hs₂ t ht
  rw [LevyStochCalc.Ito.Picard.lintegral_sq_sub_mark_eq_zero_of_ae (ν := ν) φ₁ φ₂ h] at hiso
  have hmeas : Measurable fun ω =>
      (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖₊
          : ℝ≥0∞) ^ 2 :=
    (((LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t).sub
      (LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice N ℱ hℱN φ₂ hm₂ hp₂ hs₂
        t)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hiso] with ω hω
  have hz : (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖₊
        : ℝ≥0∞) = 0 := by
    simpa using hω
  have hn : ‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN φ₂ hm₂ hp₂ hs₂ t ω‖ = 0 := by
    simpa [← ENNReal.coe_eq_zero, ← coe_nnnorm] using hz
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
