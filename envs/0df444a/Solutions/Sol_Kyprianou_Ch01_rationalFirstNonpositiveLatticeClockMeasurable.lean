-- Prove2me | solution 1 for Kyprianou.Ch01.rationalFirstNonpositiveLatticeClockMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:15:37.139838+00:00
-- url     : https://prove2.me/submissions/042965fb-b097-4793-958d-4c1356f0ee35

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The countably sampled rational first-nonpositive clock is measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t)) :
    Measurable (fun ω : Ω =>
      ⨅ r : ℚ,
        if X (Real.toNNReal (r : ℝ)) ω ≤ 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤) := by
  apply Measurable.iInf
  intro r
  apply Measurable.ite
  · exact measurableSet_le (hX (Real.toNNReal (r : ℝ))) measurable_const
  · exact measurable_const
  · exact measurable_const
