-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:42.377891+00:00
-- url     : https://prove2.me/submissions/f7162b87-e403-4b45-8c0a-cc06495d0538

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
omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in
/-- A vanishing Bielecki norm means the path map vanishes almost surely at every time of the
window. -/
theorem solution {β T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZs : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => Z u ω i)
    (h : LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) β T Z = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0 := by
  have hterm : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← h]
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (-β * t)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  have hrpow : (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hexp
  have hint : ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp hrpow with ⟨h0, _⟩ | ⟨_, hneg⟩
    · exact h0
    · exact absurd hneg (by norm_num)
  have hmeas : AEMeasurable (fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2) P :=
    (Finset.measurable_sum _ fun i _ =>
      (ENNReal.continuous_coe.measurable.comp (hZs t i).nnnorm).pow_const 2).aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hmeas).mp hint] with ω hω i
  have hle : (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 = 0 :=
    le_antisymm (le_of_le_of_eq (Finset.single_le_sum
      (f := fun j => (‖Z t ω j‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)) hω)
      zero_le
  simpa using hle
