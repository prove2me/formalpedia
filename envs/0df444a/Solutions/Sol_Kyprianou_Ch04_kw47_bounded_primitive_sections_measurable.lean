-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_bounded_primitive_sections_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:38:45.066129+00:00
-- url     : https://prove2.me/submissions/0db9651a-c7da-4b33-a15e-4fa502580593

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega] (f : Real × Omega → Real)
    (hf : Measurable f) (t : NNReal) :
    Measurable (fun w => ∫ s in Icc (0 : Real) (t : Real), f (s,w) ∂volume) := by 
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ := volume.restrict (Icc (0 : Real) (t : Real)))).measurable
