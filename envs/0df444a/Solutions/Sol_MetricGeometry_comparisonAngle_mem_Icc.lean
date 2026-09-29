-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T21:21:00.478712+00:00
-- url     : https://prove2.me/submissions/0a195c22-3b6a-4930-955b-fe5cb4ef1a43

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    0 ≤ comparisonAngle p x y ∧ comparisonAngle p x y ≤ Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
