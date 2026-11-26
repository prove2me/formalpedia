-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RationalDepthMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:49:55.50845+00:00
-- url     : https://prove2.me/submissions/43f4d2f1-1e97-4be1-b2d6-a2aeb3e79212

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Measurable real all-time depth from countably many rational coordinates. -/
theorem solution
    : Measurable (fun Y : NNReal → ℝ => (⨆ q : ℚ, ENNReal.ofReal (-Y (Real.toNNReal q))).toReal) := by
  exact ENNReal.measurable_toReal.comp
    (Measurable.iSup fun q : ℚ =>
      ENNReal.measurable_ofReal.comp (measurable_pi_apply (Real.toNNReal q)).neg)
