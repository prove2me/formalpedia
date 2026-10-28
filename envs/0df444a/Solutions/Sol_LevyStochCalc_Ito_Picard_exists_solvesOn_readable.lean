-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.exists_solvesOn_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:47.357685+00:00
-- url     : https://prove2.me/submissions/30cf5261-0a55-47fa-b844-24be4079bf01

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow
import Theorems.Thm_LevyStochCalc_Ito_Picard_exists_bieleckiWeight_rate_lt_one_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_picardSelfMapRaw_lt_top_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardSelfMapRaw_isFixedPoint_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_solvesOn_of_isFixedPoint_readable

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
/-- **Existence on a window.** For every horizon there is a càdlàg, progressively measurable
path map with a finite `S²` norm solving the equation on `[0, T]`. -/
theorem solution [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T := by
  obtain ⟨β, hβ, hq⟩ := LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one_readable (n := n) (d := d) (T := T) L hT
  set X₀ := LevyStochCalc.Ito.Picard.constantZeroProcess (n := n) P ℱ T with hX₀
  set Z := LevyStochCalc.Ito.Picard.picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hZ
  have hZm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hZa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hZb := LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Y := LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb with hY
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top_readable W N ℱ hℱW hℱN hℱ0 hnull coeffs
      hReg hLip x₀ hT hZm hZa hZb hT'
  refine ⟨Y.X, Y.measurable_path, Y.adapted, Y.cadlag_paths, hYS, ?_⟩
  refine LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint_readable W N ℱ hℱW hℱN coeffs hReg hLip x₀ hT.le
    Y.measurable_path Y.adapted Y.sup_L2 hYS ?_
  intro t ht
  exact LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint_readable W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hβ hT X₀
    hq ht
