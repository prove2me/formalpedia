-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.ae_all_windows_agree_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:32.370553+00:00
-- url     : https://prove2.me/submissions/892efba5-72ff-4b19-8eea-03e7defb19cf

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
import Theorems.Thm_LevyStochCalc_Ito_Picard_ae_all_eq_of_rightCont_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_ae_eq_of_solvesOn_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardWindow.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
section Solves
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (x₀ : Fin n → ℝ)
/-- A solution on a window is a solution on every shorter window. -/
theorem LevyStochCalc.Ito.Picard.SolvesOn.mono {X : ℝ → Ω → (Fin n → ℝ)} {T T' : ℝ} (hTT : T' ≤ T)
    (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T' := by
  obtain ⟨a, b, c, e, f, g, heq⟩ := h
  exact ⟨a, b, c, e, f, g, fun t ht => heq t ⟨ht.1, ht.2.trans hTT⟩⟩
end Solves
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
section Glue
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
/-- Window solutions on nested windows agree, almost surely, along whole paths. -/
theorem solution
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)))
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)),
      Y p.1 t ω = Y p.2 t ω := by
  rw [MeasureTheory.ae_all_iff]
  rintro ⟨j, k⟩
  have hTpos : (0 : ℝ) < min ((j : ℝ) + 1) ((k : ℝ) + 1) :=
    lt_min (by positivity) (by positivity)
  have hpt := LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn_readable W N ℱ hℱW hℱN coeffs x₀ hReg hLip (hYm j) (hYm k)
    (hYS j) (hYS k) hTpos
    (LevyStochCalc.Ito.Picard.SolvesOn.mono W N ℱ hℱW hℱN coeffs x₀ (min_le_left _ _) (hYsol j))
    (LevyStochCalc.Ito.Picard.SolvesOn.mono W N ℱ hℱW hℱN coeffs x₀ (min_le_right _ _) (hYsol k))
  refine LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont_readable (hYcad j) (hYcad k) fun t ht => ?_
  filter_upwards [hpt t ht] with ω hω
  exact funext hω
