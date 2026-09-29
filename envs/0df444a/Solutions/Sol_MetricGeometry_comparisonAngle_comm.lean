-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_comm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T23:03:04.253866+00:00
-- url     : https://prove2.me/submissions/1f1b1fd4-3a83-4a80-8787-44221ae374e4

import Definitions.Def_metric_geodesic_angle

open MetricGeometry

theorem solution {X : Type*} [PseudoMetricSpace X] (p x y : X) :
    comparisonAngle p x y = comparisonAngle p y x := by
  unfold comparisonAngle
  rw [dist_comm x y]
  ring_nf
