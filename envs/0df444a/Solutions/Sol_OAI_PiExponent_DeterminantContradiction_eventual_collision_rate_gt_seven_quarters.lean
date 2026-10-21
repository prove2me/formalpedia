-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_collision_rate_gt_seven_quarters
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:52:48.010146+00:00
-- url     : https://prove2.me/submissions/a93aedeb-137c-43ca-9cca-fb3978a9a7de

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collision_rate_tendsto_collision_limit
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collision_limit_gt_two

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    ∀ᶠ H : ℝ in atTop, 7 / 4 < collisionRate d H := by
  have hlim : 2 < collisionLimit d :=
    OAI.PiExponent.DeterminantContradiction.collision_limit_gt_two d
  have hconv : Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) :=
    OAI.PiExponent.DeterminantContradiction.collision_rate_tendsto_collision_limit d
  have hmargin : (7 : ℝ) / 4 < collisionLimit d := by
    have hquarter : (7 : ℝ) / 4 < 2 := by norm_num
    exact lt_trans hquarter hlim
  have hnear : ∀ᶠ H : ℝ in atTop, collisionRate d H ∈ Set.Ioi (7 / 4) :=
    hconv.eventually (isOpen_Ioi.mem_nhds hmargin)
  simpa only [Set.mem_Ioi] using hnear