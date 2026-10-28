-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:47.41531+00:00
-- url     : https://prove2.me/submissions/aebee222-998e-48e8-a4f0-09e31682d157

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_rawStop_congr_ae_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
section FixedPoint
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
/-- A fixed point of the frozen Picard step solves the equation on the window. -/
theorem solution
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T) {Y : ℝ → Ω → (Fin n → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hYa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hYb : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Y < ⊤)
    (hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i : Fin n,
      Y t ω i = LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT x₀ t ω i) :
    LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by
  refine ⟨LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hYm,
    LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hYa,
    LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hYm hYS,
    LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hYm,
    LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hYa,
    LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hYm hYS, ?_⟩
  intro t ht
  filter_upwards [hfix t ht,
    LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae_readable W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hYa hYb hYS hT
      ht.1 ht.2] with ω h1 h2
  intro i
  rw [h1 i, h2]
