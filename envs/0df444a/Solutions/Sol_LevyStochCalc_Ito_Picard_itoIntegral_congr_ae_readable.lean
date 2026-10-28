-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.itoIntegral_congr_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:24:42.236988+00:00
-- url     : https://prove2.me/submissions/edc9bc74-5cb5-4489-acd2-2b1f3073b9df

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
/-- The Itô integral against a Brownian motion is measurable at each time. -/
theorem LevyStochCalc.Ito.Picard.measurable_itoIntegral_slice
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H hm hp hs t ω := by
  obtain ⟨Filt, hMart⟩ :=
    LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral Wj ℱ hℱ H hm hp hs
  exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The `L²` energy of a difference vanishing a.e. on the window is zero. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_sub_eq_zero_of_ae {t : ℝ} (H₁ H₂ : Ω → ℝ → ℝ)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with s hs
  simp [hs]
/-- Integrands agreeing a.e. on `[0, t]` have a.e. equal Itô integrals at `t`. -/
theorem solution
    (Wj : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration Wj ℱ)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
    (hs₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
    (hs₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), H₁ ω s = H₂ ω s) :
    ∀ᵐ ω ∂P, LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω := by
  have hiso := LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian
    Wj ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hs₁ hs₂ ht
  rw [LevyStochCalc.Ito.Picard.lintegral_sq_sub_eq_zero_of_ae H₁ H₂ h] at hiso
  have hmeas : Measurable fun ω =>
      (‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖₊
          : ℝ≥0∞) ^ 2 :=
    (((LevyStochCalc.Ito.Picard.measurable_itoIntegral_slice Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t).sub
      (LevyStochCalc.Ito.Picard.measurable_itoIntegral_slice Wj ℱ hℱ H₂ hm₂ hp₂ hs₂
        t)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hiso] with ω hω
  have : (‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  have hn : ‖LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₁ hm₁ hp₁ hs₁ t ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegral Wj ℱ hℱ H₂ hm₂ hp₂ hs₂ t ω‖ = 0 := by
    simpa [← ENNReal.coe_eq_zero, ← coe_nnnorm] using this
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
