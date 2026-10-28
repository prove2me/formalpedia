-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:49.703983+00:00
-- url     : https://prove2.me/submissions/ca7c2d2d-ab90-4ef8-ba1d-b7462f6c10b4

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

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
omit [MeasurableSpace E] in
/-- A finite `S²` norm gives a finite Bielecki norm at weight `0`. -/
theorem solution {T : ℝ} (hT : 0 < T) {Z : ℝ → Ω → (Fin n → ℝ)}
    (hS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) :
    LevyStochCalc.Ito.Picard.bieleckiNorm (P := P) 0 T Z < ⊤ := by
  set M := ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖Z (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P with hM
  have hMfin : M < ⊤ := hS T hT
  unfold LevyStochCalc.Ito.Picard.bieleckiNorm
  have hMhalf : M ^ ((1 : ℝ) / 2) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hMfin.ne
  refine lt_of_le_of_lt ?_ hMhalf
  refine iSup_le fun t => iSup_le fun ht => ?_
  have hslice : (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ≤ M := by
    refine lintegral_mono fun ω => ?_
    exact le_iSup (fun u : Set.Icc (0 : ℝ) T =>
      ∑ i, (‖Z (u : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ⟨t, ht⟩
  calc ENNReal.ofReal (Real.exp (-(0 : ℝ) * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) := by
        simp
    _ ≤ M ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hslice (by norm_num)
