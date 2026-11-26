-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41CountIntegralV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:06:57.819539+00:00
-- url     : https://prove2.me/submissions/da9a43ef-337b-4d36-b0ce-cd43328fc0dd

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset ℕ) (A : ℕ → Set Ω)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ∑ i ∈ I, (A i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
    Measurable N ∧ (∫⁻ ω, N ω ∂P) = ∑ i ∈ I, P (A i) := by
  dsimp only
  have hm (i : ℕ) (hi : i ∈ I) :
      Measurable ((A i).indicator (fun _ : Ω => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hA i hi)
  constructor
  · exact Finset.measurable_sum I hm
  · rw [lintegral_finsetSum I hm]
    apply Finset.sum_congr rfl
    intro i hi
    exact lintegral_indicator_one (hA i hi)
