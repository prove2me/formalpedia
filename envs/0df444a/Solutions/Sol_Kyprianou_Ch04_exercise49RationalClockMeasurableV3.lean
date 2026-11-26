-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RationalClockMeasurableV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:39.420802+00:00
-- url     : https://prove2.me/submissions/da3f85d6-e2cd-4204-8d93-9ab8a6849dea

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The countably sampled real strict negative passage clock is measurable. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (Z : NNReal → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) :
    Measurable (fun ω : Ω => ⨅ q : ℚ,
      if 0 < (q : ℝ) ∧ Z (Real.toNNReal q) ω < 0 then
        (↑(Real.toNNReal q) : WithTop NNReal) else ⊤) := by
  apply Measurable.iInf
  intro q
  have hp : MeasurableSet {ω : Ω |
      0 < (q : ℝ) ∧ Z (Real.toNNReal q) ω < 0} := by
    by_cases hq : 0 < (q : ℝ)
    · simpa only [hq, true_and] using
        measurableSet_lt (hZ (Real.toNNReal q)) measurable_const
    · simp [hq]
  exact Measurable.ite hp measurable_const measurable_const
