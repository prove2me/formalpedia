-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.exists_globalSolution_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:36.885974+00:00
-- url     : https://prove2.me/submissions/ec937874-bd4d-44e0-ac72-4fa6b7b14f6f

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
import Theorems.Thm_LevyStochCalc_Ito_Picard_ae_all_windows_agree_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_cadlag_globalPatch_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_exists_solvesOn_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_progressivelyMeasurable_globalPatch_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_solvesOn_globalPatch_readable

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
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The glued path map is jointly measurable. -/
theorem LevyStochCalc.Ito.Picard.measurable_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, Measurable (Function.uncurry (Y k))) :
    Measurable (Function.uncurry (globalPatch Y)) := by
  have h : Measurable fun p : ℕ × (ℝ × Ω) => Function.uncurry (Y p.1) p.2 :=
    measurable_from_prod_countable_right fun k => hY k
  exact h.comp ((measurable_fst.nat_ceil).prodMk measurable_id)
section Glue
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map coincides, almost surely, with each member of a consistent family on that
member's window. -/
theorem LevyStochCalc.Ito.Picard.ae_globalPatch_eq {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hcons : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ,
      ∀ t ∈ Set.Icc (0 : ℝ) (min ((p.1 : ℝ) + 1) ((p.2 : ℝ) + 1)), Y p.1 t ω = Y p.2 t ω) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1), globalPatch Y t ω = Y k t ω := by
  filter_upwards [hcons] with ω hω
  intro k t ht
  refine hω (⌈t⌉₊, k) t ⟨ht.1, le_min ?_ ht.2⟩
  exact (Nat.le_ceil t).trans (by linarith)
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P] in
/-- The glued path map has a finite `S²` norm on every window. -/
theorem LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
      (‖globalPatch Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (hYS ⌈T'⌉₊ T' hT')
  filter_upwards [hagree] with ω hω
  refine le_of_eq (iSup_congr fun t => ?_)
  rw [hω ⌈T'⌉₊ (t : ℝ) ⟨t.2.1, t.2.2.trans ((Nat.le_ceil T').trans (by linarith))⟩]
/-- A solution on a window starts at the initial datum. -/
theorem LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn (x₀ : Fin n → ℝ) {X : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hT : 0 ≤ T) (h : SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) :
    ∀ᵐ ω ∂P, X 0 ω = x₀ := by
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩,
    ae_picardStep_zero W N ℱ hℱW hℱN coeffs X x₀ h.h_σ_meas h.h_σ_progMeas h.h_σ_sq
      h.h_γ_meas h.h_γ_progMeas h.h_γ_sq] with ω h1 h2
  funext i
  rw [h1 i, h2 i]
/-- **Existence of a solution on `[0, ∞)`.** The window solutions of `exists_solvesOn` are
consistent, so gluing them along `⌈t⌉₊` gives a càdlàg, progressively measurable path map with
a finite `S²` norm on every window that solves the equation on every window. -/
theorem solution [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry X)
        ∧ (∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
        ∧ (∀ᵐ ω ∂P, X 0 ω = x₀)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
            Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ (∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) := by
  have hex : ∀ k : ℕ, ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y ((k : ℝ) + 1) := fun k =>
    LevyStochCalc.Ito.Picard.exists_solvesOn_readable W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀ (by positivity)
  choose Y hYm hYa hYcad hYS hYsol using hex
  have hright : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)) := by
    intro k
    filter_upwards [hYcad k] with ω hω
    exact fun t => (hω t).1
  have hagree := LevyStochCalc.Ito.Picard.ae_globalPatch_eq (Y := Y)
    (LevyStochCalc.Ito.Picard.ae_all_windows_agree_readable W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hright hYS hYsol)
  have hsol := LevyStochCalc.Ito.Picard.solvesOn_globalPatch_readable W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hYa hagree hYS hYsol
  exact ⟨LevyStochCalc.Ito.Picard.globalPatch Y, LevyStochCalc.Ito.Picard.measurable_globalPatch hYm,
    fun i => LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch_readable hYa i,
    LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn W N ℱ hℱW hℱN coeffs x₀ zero_le_one (hsol 1),
    LevyStochCalc.Ito.Picard.cadlag_globalPatch_readable hagree hYcad,
    LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top hagree hYS, hsol⟩
