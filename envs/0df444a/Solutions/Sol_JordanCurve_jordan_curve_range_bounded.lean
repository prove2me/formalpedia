-- Prove2me | solution 1 for JordanCurve.jordan_curve_range_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T00:46:03.402902+00:00
-- url     : https://prove2.me/submissions/0bac0b99-23f0-4242-81b2-7006d5ec6838

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded

theorem solution
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) :
    Bornology.IsBounded (Set.range γ) := by
  simpa only [Set.image_univ] using (isCompact_univ.image hγ).isBounded
