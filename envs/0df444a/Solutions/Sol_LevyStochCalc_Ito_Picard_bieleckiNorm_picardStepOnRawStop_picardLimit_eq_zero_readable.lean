-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:39.038817+00:00
-- url     : https://prove2.me/submissions/e26e1945-896e-4224-8e96-6f60a22a3cab

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_picardStepOnStop_sub_rawStop_le_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_measurable_picardStepOnRawStop_slice_readable

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
/-- **The limit of the Picard iterates is a fixed point of the Picard step**: the Bielecki
distance between the step along the limit and the limit itself is zero. -/
theorem solution {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : LevyStochCalc.Ito.Picard.SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
        LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
            (LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
              x₀ hT X₀)
            (LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
              hβ hT X₀ hq)
            hT.le x₀ t ω i
          - LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) = 0 := by
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  set Y := LevyStochCalc.Ito.Picard.picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hYdef
  have hYm := LevyStochCalc.Ito.Picard.measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Φ := LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT.le x₀ with hΦdef
  set D := (1 - q)⁻¹ * LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
      (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
        - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i)
    with hDdef
  have hDfin : D ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne
  have hiter := fun k => LevyStochCalc.Ito.Picard.bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull
    coeffs hReg hLip x₀ hβ hT X₀ hq k
  have hbound : ∀ k : ℕ, LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i - Y t ω i)
      ≤ q ^ (k + 1) * D + q ^ (k + 1) * D := by
    intro k
    have hXm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω =>
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i :=
      fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
          (k + 1)).measurable_path t i
    have hΦm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Φ t ω i := fun t i =>
      LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice_readable W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        hYm hYa hYb hT.le t i
    have hYsl : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i :=
      fun t i => LevyStochCalc.Ito.Picard.measurable_slice_of_uncurry hYm t i
    have hEq : (fun t ω i => Φ t ω i - Y t ω i)
        = fun t (ω : Ω) =>
          (fun i => Φ t ω i
            - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
          + fun i =>
            (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
              - Y t ω i := by
      funext t ω i
      simp [Pi.add_apply, sub_add_sub_cancel]
    have hadd := LevyStochCalc.Ito.Picard.bieleckiNorm_add_le (P := P) β T
      (fun t ω => fun i => Φ t ω i
        - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
      (fun t ω => fun i =>
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - Y t ω i)
      (LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hΦm t i).sub (hXm t i))
      (LevyStochCalc.Ito.Picard.bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hXm t i).sub (hYsl t i))
    have hcongr : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        = LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i =>
            LevyStochCalc.Ito.Picard.picardStepOnStop W N hℱW hℱN coeffs hReg hLip
              (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) hT.le x₀ t ω i
              - Φ t ω i) := by
      rw [LevyStochCalc.Ito.Picard.bieleckiNorm_sub_comm (P := P) β T]
      refine LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae (P := P) β T fun t => ?_
      filter_upwards [LevyStochCalc.Ito.Picard.picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
        (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) t] with ω hω
      funext i
      have hunfold : (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
            (k + 1)).X t ω
          = (LevyStochCalc.Ito.Picard.picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k)).X t ω := rfl
      rw [hunfold, hω]
    have hfirst : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (LevyStochCalc.Ito.Picard.picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        ≤ q ^ (k + 1) * D := by
      rw [hcongr]
      refine le_trans (LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le_readable W N ℱ' hℱW hℱN
        coeffs hReg hLip hYm hYa hYb x₀ hβ hT _) ?_
      refine le_trans (mul_le_mul' le_rfl (hiter k)) (le_of_eq ?_)
      rw [← mul_assoc, ← pow_succ']
    rw [hEq]
    exact hadd.trans (add_le_add hfirst (hiter (k + 1)))
  have htend : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D + q ^ (k + 1) * D)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun k : ℕ => q ^ (k + 1)) Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    have hm : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D) Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.mul_const hp (Or.inr hDfin)
    simpa using hm.add hm
  exact le_antisymm (ge_of_tendsto' htend hbound) zero_le
