-- Prove2me | solution 2 for Kyprianou.Ch03.temperedStableMeasureReflectionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:51:50.063096+00:00
-- url     : https://prove2.me/submissions/e44a64cf-c487-425d-88c9-4e52a3263a9f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isLevyMeasure_iff
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure ℝ) (hm : IsLevyMeasure (mu.map (fun x : ℝ => -x))) :
    IsLevyMeasure mu := by
  rw [IsLevyMeasure.isLevyMeasure_iff] at hm ⊢
  constructor
  · have hzero := hm.1
    rw [Measure.map_apply measurable_neg (measurableSet_singleton _)] at hzero
    have he : (fun x : ℝ => -x) ⁻¹' ({0} : Set ℝ) = {0} := by
      ext x
      simp
    rwa [he] at hzero
  · have hi := hm.2
    rw [lintegral_map (by fun_prop) measurable_neg] at hi
    simpa only [neg_sq] using hi
