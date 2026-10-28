-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_diff_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:24:41.160317+00:00
-- url     : https://prove2.me/submissions/50f8fdaa-ae59-49ca-a6ca-b4fe87d433d6

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardContractionFixedPoint.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
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
variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)
omit [ℱ'.IsRightContinuous] in
/-- **The Picard step contracts between two raw state processes.** -/
theorem solution
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
        LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
          - LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Z₁ t ω i - Z₂ t ω i) := by
  have h₁sm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z₁ (min s T) ω) :=
    h₁m.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have h₂sm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z₂ (min s T) ω) :=
    h₂m.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have h₁e := LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top h₁m h₁b hT.le
  have h₂e := LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top h₂m h₂b hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => Z₁ (min s T) ω - Z₂ (min s T) ω) :=
    (h₁sm.comp (measurable_snd.prodMk measurable_fst)).sub
      (h₂sm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T
      (fun t ω i => Z₁ (min t T) ω i - Z₂ (min t T) ω i)
      = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Z₁ t ω i - Z₂ t ω i) :=
    LevyStochCalc.Ito.Picard.bieleckiNorm_min (P := P) β T fun t ω i => Z₁ t ω i - Z₂ t ω i
  rw [← hrhs]
  exact LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_diff_le W N ℱ' hℱW hℱN coeffs hLip
    (fun s ω => Z₁ (min s T) ω) (fun s ω => Z₂ (min s T) ω) x₀
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg h₁m T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg h₁a T)
    (fun i j _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg h₁m T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg h₁a T)
    (fun i _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i hT')
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg h₂m T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg h₂a T)
    (fun i j _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i j hT')
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg h₂m T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg h₂a T)
    (fun i _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i hT')
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg h₁m T)
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg h₂m T)
    hdiffm.norm
    (fun i b hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁e i hb)
    (fun i b hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂e i hb)
    (fun b _ => LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy h₁sm h₂sm h₁e h₂e b)
    hdiffm hβ hT
