-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:13.587153+00:00
-- url     : https://prove2.me/submissions/31ff6e5f-2dd5-4881-bf5c-0fe7c2851a05

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardSelfMapRaw_ae_eq_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardSelfMapRaw_picardLimit_ae_eq_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_picardStepOnRawStop_congr_ae_readable

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
/-- **The fixed point is a solution of the Picard equation along its own path.** On the window,
the process agrees almost surely with the Picard step taken along itself, frozen at the horizon.
-/
theorem solution {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : LevyStochCalc.Ito.Picard.SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      (LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
          (LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
          (LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
            x₀ hT X₀)
          (LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
            hβ hT X₀ hq)).X t ω i
        = LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).measurable_path
            (fun i' =>
              (LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
                (LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
                (LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
                  hLip x₀ hT X₀)
                (LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                  x₀ hβ hT X₀ hq)).adapted i')
            (LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).sup_L2
            hT.le x₀ t ω i := by
  have hYm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Xhat := LevyStochCalc.Ito.Picard.picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hYm hYa hYb
    with hXhat
  have heq : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i,
      LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ u ω i
        = Xhat.X u ω i := by
    intro u hu
    filter_upwards [LevyStochCalc.Ito.Picard.picardSelfMapRaw_picardLimit_ae_eq_readable W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT X₀ hq hu] with ω hω i
    exact (hω i).symm
  have hcongr := LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae_readable W N ℱ' hℱW hℱN coeffs hReg hLip x₀
    hYm hYa hYb Xhat.measurable_path (fun i' => Xhat.adapted i') Xhat.sup_L2 heq hβ hT ht
  filter_upwards [LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq_readable W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
    hYm hYa hYb t, hcongr] with ω hmod hc i
  rw [congrFun hmod i]
  exact hc i
