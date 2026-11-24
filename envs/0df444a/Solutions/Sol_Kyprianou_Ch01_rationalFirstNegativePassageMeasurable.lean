-- Prove2me | solution 1 for Kyprianou.Ch01.rationalFirstNegativePassageMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T17:23:40.626458+00:00
-- url     : https://prove2.me/submissions/6ec5a22c-5987-4940-b290-fda089724e27

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The countably sampled rational first-negative clock is measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω =>
      ⨅ r : ℚ,
        if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) := by
  apply Measurable.iInf
  intro r
  -- `0 < r` is ω-independent; fold into a measurable predicate on ω via ∧
  have hpred :
      MeasurableSet
        {ω : Ω | 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0} := by
    by_cases hr : 0 < (r : ℝ)
    · simpa [hr] using
        measurableSet_lt (hX (Real.toNNReal (r : ℝ))) measurable_const
    · simp [hr]
  exact Measurable.ite hpred measurable_const measurable_const
