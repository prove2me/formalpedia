-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46MappedClockNullSingletonV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:18:49.347732+00:00
-- url     : https://prove2.me/submissions/70d8eecc-16f7-4d29-a7f9-c8be403164da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (T : NNReal) :
    NullSingletonClass (((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal) := by
  constructor
  intro x
  rw [Measure.map_apply measurable_real_toNNReal (measurableSet_singleton x),
    Measure.restrict_apply (measurable_real_toNNReal (measurableSet_singleton x))]
  apply measure_mono_null (t := {(x : Real)}) _ (measure_singleton _)
  intro r hr
  have he : Real.toNNReal r = x := hr.1
  change r = (x : Real)
  rw [← he, Real.coe_toNNReal r hr.2.1]
