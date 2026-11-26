-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49EmbeddedIndependentV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:49:25.023953+00:00
-- url     : https://prove2.me/submissions/83acba08-1c44-4e8e-bb7c-35f88b290d67

import Mathlib.Probability.Independence.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω E ι : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (f : ι → E → ℝ)
    (h : iIndepFun (fun i w => f i (j w)) P) :
    iIndepFun f (Measure.map j P) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S A hA
  simp_rw [hj.map_apply,Set.preimage_iInter,← Set.preimage_comp]
  exact h.measure_inter_preimage_eq_mul S hA
