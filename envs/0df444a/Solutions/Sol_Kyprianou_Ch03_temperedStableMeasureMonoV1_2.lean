-- Prove2me | solution 2 for Kyprianou.Ch03.temperedStableMeasureMonoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:57:36.43508+00:00
-- url     : https://prove2.me/submissions/79c0948f-797d-498a-8321-05a455abc35f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure ℝ) (hle : mu ≤ nu) (hn : IsLevyMeasure nu) :
    IsLevyMeasure mu := by
  refine ⟨le_antisymm (by simpa [hn.1] using Measure.le_iff.mp hle {0} (measurableSet_singleton 0)) bot_le, ?_⟩
  exact lt_of_le_of_lt (lintegral_mono' hle le_rfl) hn.2
