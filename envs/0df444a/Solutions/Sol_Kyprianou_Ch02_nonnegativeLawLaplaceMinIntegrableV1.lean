-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLawLaplaceMinIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:27.478621+00:00
-- url     : https://prove2.me/submissions/19b1692b-3908-444f-b72d-82067cb9ba66

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) Q := by
  apply (integrable_const (1 : ℝ)).mono'
  · exact (show Continuous (fun x : ℝ => min (1 : ℝ) |x|) by fun_prop).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (abs_nonneg x))]
    exact min_le_left _ _
