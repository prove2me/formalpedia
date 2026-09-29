-- Prove2me | solution 1 for MetricGeometry.germAngle_pseudoMetric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:52:18.165252+00:00
-- url     : https://prove2.me/submissions/05465188-1c87-4244-8fb1-f94f7640c02c

import Definitions.Def_space_of_directions
import Theorems.Thm_MetricGeometry_alexandrovAngle_comm
import Theorems.Thm_MetricGeometry_alexandrovAngle_mem_Icc
import Theorems.Thm_MetricGeometry_alexandrovAngle_triangle_segment
import Theorems.Thm_MetricGeometry_alexandrovAngle_geodesicSegment_self_eq_zero

open MetricGeometry

universe u

theorem solution {X : Type u} [PseudoMetricSpace X] (p : X) :
    (∀ g : GeodesicGerm p, germAngle g g = 0) ∧
    (∀ g1 g2 : GeodesicGerm p, germAngle g1 g2 = germAngle g2 g1) ∧
    (∀ g1 g2 g3 : GeodesicGerm p,
      germAngle g1 g3 ≤ germAngle g1 g2 + germAngle g2 g3) ∧
    (∀ g1 g2 : GeodesicGerm p, germAngle g1 g2 ∈ Set.Icc 0 Real.pi) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    exact MetricGeometry.alexandrovAngle_geodesicSegment_self_eq_zero p g.endpoint
      g.toFun g.isSegment g.nondegenerate
  · intro g1 g2
    exact MetricGeometry.alexandrovAngle_comm p g1.toFun g2.toFun
  · intro g1 g2 g3
    have htri := MetricGeometry.alexandrovAngle_triangle_segment p g2.endpoint
      g1.endpoint g3.endpoint g2.toFun g1.toFun g3.toFun g2.isSegment g1.isSegment
      g3.isSegment g2.nondegenerate g1.nondegenerate g3.nondegenerate
    unfold germAngle
    rw [MetricGeometry.alexandrovAngle_comm p g1.toFun g2.toFun]
    exact htri
  · intro g1 g2
    exact MetricGeometry.alexandrovAngle_mem_Icc p g1.toFun g2.toFun
