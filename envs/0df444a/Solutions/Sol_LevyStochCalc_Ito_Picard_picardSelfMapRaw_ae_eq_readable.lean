-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:24:16.297985+00:00
-- url     : https://prove2.me/submissions/ec2dd793-59a4-4a7c-9e7b-3a39223fba1e

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardOutputModification

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardOutputModification.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section SelfMap
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
/-- The raw self-map's path is a modification of the Picard step along the raw process. -/
theorem solution
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z < ⊤) (t : ℝ) :
    (LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X t
      =ᵐ[P] LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t :=
  Classical.choose_spec (LevyStochCalc.Ito.Picard.exists_sBoundedProcess_picardStep W ℱ hℱW coeffs
    (fun s ω => Z (min s T) ω)
    (LevyStochCalc.Ito.Picard.measurable_sigma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT')
    N hℱN x₀
    (LevyStochCalc.Ito.Picard.measurable_gamma_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT')
    hℱ0 hnull
    (LevyStochCalc.Ito.Picard.measurable_mu_rawStop coeffs hReg hZm T)
    (LevyStochCalc.Ito.Picard.progressivelyMeasurable_mu_rawStop coeffs hReg hZa T)
    (fun i _ hb => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hb)
    (fun i => LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)
    (fun i j => LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i j hT)
    (fun i => LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top hZm hZb hT.le) i hT)) t
