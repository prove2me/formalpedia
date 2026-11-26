-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49AddLinearLevyV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:06:45.256499+00:00
-- url     : https://prove2.me/submissions/38031aec-1847-44ce-a0e8-8e3aaa6b1f77

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_increments_add_linear_drift
import Theorems.Thm_AvramDividend_Classical_avram_a06_stationary_increments_add_linear_drift
import Theorems.Thm_ProbabilityTheory_IsCadlag_add
import Theorems.Thm_Continuous_isCadlag
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]
theorem solution (P : Measure Ω) (Z : NNReal → Ω → ℝ) (hZ : IsLevyProcess Z P) (b : ℝ) :
    IsLevyProcess (fun t w => Z t w + b * (t : ℝ)) P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext w
    simp [hZ.start_zero]
  · exact avram_a06_independent_increments_add_linear_drift P Z b hZ.indep_increments
  · exact avram_a06_stationary_increments_add_linear_drift P Z b hZ.stationary_increments
  · filter_upwards [hZ.cadlag_ae] with w hw
    exact hw.add (Continuous.isCadlag (continuous_const.mul continuous_subtype_val))
