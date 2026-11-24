-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_sampled_upper_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:01:42.166188+00:00
-- url     : https://prove2.me/submissions/9b2b10c3-74f4-430b-93f3-c5c119bcaf9b


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Source record regeneration. -/
theorem solution :
    ∀ (s : ℕ → ℝ≥0) (c : ℝ),
      Measurable (fun f : ℝ≥0 → ℝ =>
        ⨅ i : ℕ, if c < f (s i) then (s i : ℝ≥0∞) else ⊤) := by
  intro s c
  apply Measurable.iInf
  intro i
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply _))
    measurable_const measurable_const
