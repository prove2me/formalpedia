-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:24:33.272114+00:00
-- url     : https://prove2.me/submissions/f4acde89-e3ba-4354-ac0f-a84b040b4b01

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionEstimate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionEstimate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
omit [ℱ'.IsRightContinuous] in
/-- **The Picard step contracts between a process of the space and a raw state process.** -/
theorem solution {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z < ⊤)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X : LevyStochCalc.Ito.Picard.SBoundedProcess (n := n) P ℱ' T) :
    LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
        LevyStochCalc.Ito.Picard.picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) := by
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hXe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun c =>
    lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stop_le X hT.le c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2))
  have hZe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Z (min s T) ω) :=
    (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
      (hZsm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T
      (fun t ω i => X.stop.X t ω i - Z (min t T) ω i)
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) :=
    LevyStochCalc.Ito.Picard.bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Z t ω i
  rw [← hrhs]
  exact LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_diff_le W N ℱ' hℱW hℱN coeffs hLip X.stop.X
    (fun s ω => Z (min s T) ω) x₀
    (fun i j => LevyStochCalc.Ito.Picard.measurable_sigma_stop coeffs hReg X i j)
    (fun i j => LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => LevyStochCalc.Ito.Picard.measurable_gamma_stop coeffs hReg X i)
    (fun i => LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i hT')
    (fun i => LevyStochCalc.Ito.Picard.measurable_mu_stop coeffs hReg X i)
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T)
    hdiffm.norm
    (fun i b hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZe i hb)
    (fun b _ => LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy X.stop.measurable_path hZsm hXe hZe b)
    hdiffm hβ hT
