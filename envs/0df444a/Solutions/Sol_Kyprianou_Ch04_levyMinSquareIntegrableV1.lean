-- Prove2me | solution 1 for Kyprianou.Ch04.levyMinSquareIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:18:32.541912+00:00
-- url     : https://prove2.me/submissions/dd31e2ef-e5c1-4b4d-b90a-277c36972e80

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option autoImplicit false

/-- The canonical bounded quadratic Lévy envelope is integrable. -/
theorem solution (ν : Measure ℝ) (hν : IsLevyMeasure ν) :
    Integrable (fun z : ℝ => min 1 (z^2)) ν := by
  refine ⟨(measurable_const.min (measurable_id.pow_const 2)).aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => le_min zero_le_one
    (sq_nonneg z))).2 hν.2
