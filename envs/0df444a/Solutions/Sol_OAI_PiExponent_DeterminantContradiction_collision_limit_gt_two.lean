-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collision_limit_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:56:19.19698+00:00
-- url     : https://prove2.me/submissions/01a71ccd-6855-4f96-8c94-86241b5165ea

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    2 < collisionLimit d := by
  simpa [collisionLimit] using d.collision_margin