-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.picardStep_jump_congr_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:04.457537+00:00
-- url     : https://prove2.me/submissions/5dece1eb-ff0f-4247-93de-cdefd6098613

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality
import Theorems.Thm_LevyStochCalc_Ito_Picard_compensatedIntegral_congr_ae_readable

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
section Step
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
/-- The compensated-Poisson component at `t` only reads its input on `[0, t]`. -/
theorem solution
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = LevyStochCalc.Ito.Picard.picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  have hcomp : ∀ i : Fin n, ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω' s e => coeffs.γ s (X s ω') e i)
          (h_γ_meas_X i) (h_γ_progMeas_X i) (h_γ_sq_X i) t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω' s e => coeffs.γ s (Y s ω') e i)
          (h_γ_meas_Y i) (h_γ_progMeas_Y i) (h_γ_sq_Y i) t ω := by
    intro i
    refine LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae_readable N ℱ hℱN _ _ _ _ _ _ _ _ ht ?_
    filter_upwards [hXY] with ω hω
    filter_upwards [hω] with s hs
    funext e
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  funext i
  exact hω i
