-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:06:23.722528+00:00
-- url     : https://prove2.me/submissions/4a067a7b-48d4-4ed3-872d-d1952030644e

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoQuadVarRiemannTermBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section CellSums
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- **`L¹` bound for a weighted sum of cell terms.** With weights bounded by `Kw` and cell terms
whose first absolute moments are all at most `ρ`, the weighted sum has first absolute moment at
most `N·Kw·ρ`. -/
theorem solution (N : ℕ) (w R : ℕ → Ω → ℝ)
    (hwm : ∀ i, Measurable (w i)) (hRm : ∀ i, Measurable (R i))
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (hwb : ∀ (i : ℕ) (ω : Ω), |w i ω| ≤ Kw)
    (hRint : ∀ i, Integrable (fun ω => |R i ω|) P)
    {ρ : ℝ} (hRle : ∀ i, ∫ ω, |R i ω| ∂P ≤ ρ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P ≤ (N : ℝ) * (Kw * ρ) := by
  have hdom : Integrable (fun ω => ∑ i ∈ Finset.range N, Kw * |R i ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => (hRint i).const_mul _
  have hmeas : Measurable fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω :=
    Finset.measurable_sum _ fun i _ => (hwm i).mul (hRm i)
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, w i ω * R i ω|
      ≤ ∑ i ∈ Finset.range N, Kw * |R i ω| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hwb i ω) (abs_nonneg _)
  have hint : Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P := by
    refine hdom.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hint, ?_⟩
  calc ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P
      ≤ ∫ ω, ∑ i ∈ Finset.range N, Kw * |R i ω| ∂P :=
        MeasureTheory.integral_mono hint.abs hdom hpt
    _ = ∑ i ∈ Finset.range N, Kw * ∫ ω, |R i ω| ∂P := by
        rw [MeasureTheory.integral_finsetSum _ fun i _ => (hRint i).const_mul _]
        exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
    _ ≤ ∑ _i ∈ Finset.range N, Kw * ρ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hRle i) hKw0
    _ = (N : ℝ) * (Kw * ρ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
