-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.clampMesh_mono_window_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:16.554093+00:00
-- url     : https://prove2.me/submissions/0f96ca56-6512-4129-88d2-f1936647e14a

import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology
universe u
section Mesh
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- The clamping mesh grows with the window. -/
theorem solution (P : Measure Ω) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) {T T' : ℝ} (hTT' : T ≤ T') (j : ℕ) :
    LevyStochCalc.Brownian.Ito.clampMesh P H b T j ≤ LevyStochCalc.Brownian.Ito.clampMesh P H b T' j := by
  unfold LevyStochCalc.Brownian.Ito.clampMesh
  refine Finset.sum_le_sum fun p _ => ?_
  have hmonoD : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.Brownian.Ito.clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Brownian.Ito.clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    MeasureTheory.lintegral_mono fun ω =>
      MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right hTT')
  have hmonoH : ∀ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun k => MeasureTheory.lintegral_mono fun ω =>
      MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right hTT')
  have hT : ENNReal.ofReal T ≤ ENNReal.ofReal T' := ENNReal.ofReal_le_ofReal hTT'
  gcongr
