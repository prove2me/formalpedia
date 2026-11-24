-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableMeasureReflectionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:43:05.715973+00:00
-- url     : https://prove2.me/submissions/2d10b42f-3360-4f8b-950d-88908ad22d19

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure ℝ) (hm : IsLevyMeasure (mu.map (fun x : ℝ => -x))) :
    IsLevyMeasure mu := by
  refine ⟨?_, ?_⟩
  · have h := hm.1
    rw [Measure.map_apply measurable_neg (measurableSet_singleton (0 : ℝ))] at h
    simpa using h
  · have h := hm.2
    rw [lintegral_map (by fun_prop) measurable_neg] at h
    simpa only [neg_sq] using h
