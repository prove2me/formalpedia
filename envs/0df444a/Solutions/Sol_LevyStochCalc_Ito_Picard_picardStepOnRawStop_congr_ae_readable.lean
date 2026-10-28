-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:39.996824+00:00
-- url     : https://prove2.me/submissions/08eb6ce9-5624-4958-b331-41b850de7484

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardContractionFixedPoint
import Theorems.Thm_LevyStochCalc_Ito_Picard_ae_eq_zero_of_bieleckiNorm_eq_zero_readable
import Theorems.Thm_LevyStochCalc_Ito_Picard_bieleckiNorm_picardStepOnRawStop_diff_le_readable
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
omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in
/-- A path map vanishing almost surely at every time of the window has zero Bielecki norm. -/
theorem LevyStochCalc.Ito.Picard.bieleckiNorm_eq_zero_of_ae (β T : ℝ) {Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0) :
    bieleckiNorm (P := P) β T Z = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) zero_le
  have hz : (fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] 0 := by
    filter_upwards [h t ht] with ω hω
    simp [hω]
  rw [lintegral_congr_ae hz]
  simp
omit [ℱ'.IsRightContinuous] in
/-- **The Picard step respects almost sure equality of its input.** -/
theorem solution
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z₁ t ω i = Z₂ t ω i)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
        = LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i := by
  have hin : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun u ω i => Z₁ u ω i - Z₂ u ω i) = 0 := by
    refine LevyStochCalc.Ito.Picard.bieleckiNorm_eq_zero_of_ae (P := P) β T fun u hu => ?_
    filter_upwards [heq u hu] with ω hω i
    rw [hω i, sub_self]
  have hout : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T (fun u ω i =>
      LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ u ω i
        - LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ u ω i) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_diff_le_readable W N ℱ' hℱW hℱN coeffs hReg hLip
      x₀ h₁m h₁a h₁b h₂m h₂a h₂b hβ hT) ?_
    rw [hin, mul_zero]
  have hslice : ∀ (u : ℝ) (i : Fin n), Measurable fun ω =>
      LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ u ω i
        - LevyStochCalc.Ito.Picard.picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ u ω i :=
    fun u i => (LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice_readable W N ℱ' hℱW hℱN coeffs hReg hLip x₀
      h₁m h₁a h₁b hT.le u i).sub
      (LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice_readable W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        h₂m h₂a h₂b hT.le u i)
  filter_upwards [LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero_readable (P := P) hslice hout ht] with ω hω i
  exact sub_eq_zero.mp (hω i)
