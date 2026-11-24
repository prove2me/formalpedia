-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableMeasureMonoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:51:36.229645+00:00
-- url     : https://prove2.me/submissions/ae2f6844-277e-44cc-8a50-d13a30040938

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isLevyMeasure_iff
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure ℝ) (hle : mu ≤ nu) (hn : IsLevyMeasure nu) :
    IsLevyMeasure mu := by
  rw [IsLevyMeasure.isLevyMeasure_iff] at hn ⊢
  refine ⟨le_antisymm ((Measure.le_iff.mp hle _ (measurableSet_singleton _)).trans_eq hn.1)
    bot_le, ?_⟩
  exact (lintegral_mono' hle le_rfl).trans_lt hn.2
