-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.solvesOn_globalPatch_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:03.750986+00:00
-- url     : https://prove2.me/submissions/57e860a0-d712-4435-a4a3-a5abf93bf794

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_diffusion_congr_ae_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_jump_congr_ae_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_progressivelyMeasurable_globalPatch_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
section
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
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The drift component at `t` only reads its input on `[0, t]`. -/
theorem LevyStochCalc.Ito.Picard.picardStep_drift_congr_ae {t : ℝ}
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P, picardStep_drift coeffs X x₀ t ω = picardStep_drift coeffs Y x₀ t ω := by
  filter_upwards [hXY] with ω hω
  have hω' : ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) t → X s ω = Y s ω :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : (fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
      = fun i : Fin n => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Y s ω) i := by
    funext i
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω'] with s hs hsmem
    rw [hs hsmem]
  simp only [picardStep_drift, hint]
/-- **The Picard step is local.** Inputs agreeing a.e. on `[0, t]` give a.e. equal steps at `t`. -/
theorem LevyStochCalc.Ito.Picard.picardStep_congr_ae
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i)
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), X s ω = Y s ω) :
    ∀ᵐ ω ∂P,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        = picardStep W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω := by
  filter_upwards [picardStep_drift_congr_ae coeffs X Y x₀ hXY,
    picardStep_diffusion_congr_ae_readable W ℱ hℱW coeffs X Y h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y ht hXY,
    picardStep_jump_congr_ae_readable N ℱ hℱN coeffs X Y h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht hXY] with ω h1 h2 h3
  simp only [picardStep, h1, h2, h3]
end Step
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
/-- **The glued path map solves the equation on every window.** -/
theorem solution
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hYm : ∀ k, Measurable (Function.uncurry (Y k)))
    (hYa : ∀ k, ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      LevyStochCalc.Ito.Picard.globalPatch Y t ω = Y k t ω)
    (hYS : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y k (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hYsol : ∀ k : ℕ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ (Y k) ((k : ℝ) + 1)) (T : ℝ) :
    LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ (LevyStochCalc.Ito.Picard.globalPatch Y) T := by
  have hpm := LevyStochCalc.Ito.Picard.measurable_globalPatch hYm
  have hpa := fun i => LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch_readable hYa i
  have hpS := LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top hagree hYS
  refine ⟨LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm,
    LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa,
    LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS,
    LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm,
    LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa,
    LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS, ?_⟩
  intro t ht
  have htk : t ≤ (⌈t⌉₊ : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
  have heqn := (hYsol ⌈t⌉₊).eqn t ⟨ht.1, htk⟩
  rcases ht.1.lt_or_eq with ht0 | ht0
  · have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Y ⌈t⌉₊ s ω = LevyStochCalc.Ito.Picard.globalPatch Y s ω := by
      filter_upwards [hagree] with ω hω
      refine (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun s hs => ?_)
      exact (hω ⌈t⌉₊ s ⟨hs.1, hs.2.trans htk⟩).symm
    have hcongr := LevyStochCalc.Ito.Picard.picardStep_congr_ae W N ℱ hℱW hℱN coeffs (Y ⌈t⌉₊) (LevyStochCalc.Ito.Picard.globalPatch Y) x₀
      (hYsol ⌈t⌉₊).h_σ_meas (hYsol ⌈t⌉₊).h_σ_progMeas (hYsol ⌈t⌉₊).h_σ_sq
      (hYsol ⌈t⌉₊).h_γ_meas (hYsol ⌈t⌉₊).h_γ_progMeas (hYsol ⌈t⌉₊).h_γ_sq
      (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm)
      (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
      (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
      (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm)
      (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
      (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS) ht0 hae
    filter_upwards [heqn, hagree, hcongr] with ω h1 h2 h3
    intro i
    rw [h2 ⌈t⌉₊ t ⟨ht.1, htk⟩, h1 i, h3]
  · subst ht0
    filter_upwards [heqn, hagree,
      LevyStochCalc.Ito.Picard.ae_picardStep_zero W N ℱ hℱW hℱN coeffs (Y ⌈(0 : ℝ)⌉₊) x₀
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_meas (hYsol ⌈(0 : ℝ)⌉₊).h_σ_progMeas
        (hYsol ⌈(0 : ℝ)⌉₊).h_σ_sq (hYsol ⌈(0 : ℝ)⌉₊).h_γ_meas
        (hYsol ⌈(0 : ℝ)⌉₊).h_γ_progMeas (hYsol ⌈(0 : ℝ)⌉₊).h_γ_sq,
      LevyStochCalc.Ito.Picard.ae_picardStep_zero W N ℱ hℱW hℱN coeffs (LevyStochCalc.Ito.Picard.globalPatch Y) x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hpm)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hpa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)
        (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hpm)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hpa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hpm hpS)] with ω h1 h2 h3 h4
    intro i
    rw [h2 ⌈(0 : ℝ)⌉₊ 0 ⟨le_rfl, htk⟩, h1 i, h3 i, h4 i]
