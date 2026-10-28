-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:02.12964+00:00
-- url     : https://prove2.me/submissions/a57e3096-63b8-49c2-ac74-45a46bcc0d6c

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardLocality
import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_diffusion_congr_ae_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_jump_congr_ae_readable

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
/-- Freezing a path map at a horizon does not change the Picard step at earlier times. -/
theorem solution
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z < ⊤)
    (hZS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hT : 0 ≤ T) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P,
      LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω
        = LevyStochCalc.Ito.Picard.picardStep W N ℱ hℱW hℱN coeffs Z x₀
            (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hZm)
            (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
            (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hZm)
            (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
            (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
            t ω := by
  have hfrozenm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  rcases ht0.lt_or_eq with ht0' | ht0'
  swap
  · subst ht0'
    filter_upwards [LevyStochCalc.Ito.Picard.ae_picardStep_zero W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
        (fun i j _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
          (Z := fun s ω => Z (min s T) ω) hfrozenm
          (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i j hb)
        (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
        (fun i _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
          (Z := fun s ω => Z (min s T) ω) hfrozenm
          (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i hb),
      LevyStochCalc.Ito.Picard.ae_picardStep_zero W N ℱ hℱW hℱN coeffs Z x₀
        (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hZm)
        (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
        (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hZm)
        (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
        (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)] with ω h1 h2
    funext i
    rw [h2 i]
    exact h1 i
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      (fun (s : ℝ) (ω : Ω) => Z (min s T) ω) s ω = Z s ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    simp only [min_eq_left (hs.2.trans htT)]
  exact LevyStochCalc.Ito.Picard.picardStep_congr_ae W N ℱ hℱW hℱN coeffs (fun s ω => Z (min s T) ω) Z x₀
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hfrozenm (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i j hb)
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hfrozenm (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT) i hb)
    (LevyStochCalc.Ito.Picard.measurable_sigma_comp_state coeffs hReg hZm)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state coeffs hReg hZa)
    (LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
    (LevyStochCalc.Ito.Picard.measurable_gamma_comp_state coeffs hReg hZm)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state coeffs hReg hZa)
    (LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2 coeffs hReg hLip hZm hZS)
    ht0' hae
