-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41MappedTimeCountableNullV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:22:55.142802+00:00
-- url     : https://prove2.me/submissions/12e87d42-6024-4567-b8b9-3a68571f4c71

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
theorem solution
    (T : NNReal) (S : Set NNReal) (hS : S.Countable) :
    ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).map Real.toNNReal) S = 0 := by
  rw [Measure.map_apply (by fun_prop) hS.measurableSet,
    Measure.restrict_apply (hS.measurableSet.preimage (by fun_prop))]
  apply Set.Countable.measure_zero
  apply (hS.image (fun t : NNReal => (t : ℝ))).mono
  intro r hr
  refine ⟨Real.toNNReal r, hr.1, ?_⟩
  exact Real.coe_toNNReal r hr.2.1
