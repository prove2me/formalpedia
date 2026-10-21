-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_mean_le_theta_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:54:33.685999+00:00
-- url     : https://prove2.me/submissions/5435b152-9f48-4667-9f49-83ba7dea51dc

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMean_bounds

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℝ) (hH : 0 < H) :
    actualMean d H ≤ d.base.theta := by
  exact (OAI.PiExponent.DeterminantContradiction.actualMean_bounds d H hH).2
