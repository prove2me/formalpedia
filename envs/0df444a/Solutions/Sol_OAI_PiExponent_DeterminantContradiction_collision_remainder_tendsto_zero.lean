-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collision_remainder_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:05:36.93638+00:00
-- url     : https://prove2.me/submissions/fa2b1056-019f-4ee3-8056-0e8cccb9ed16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_actualRowCount_div_tendsto_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_const_div_tendsto_zero

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => OAI.PiExponent.Collision.collisionRemainder
      (actualRowCount d H) H) atTop (𝓝 0) := by
  change Tendsto (fun H : ℝ =>
    (Real.log (actualRowCount d H : ℝ) + Real.log 2 / 4 -
      Real.log (1 - OAI.PiExponent.Collision.collisionRatio)) / H) atTop (𝓝 0)
  have hlog := OAI.PiExponent.DeterminantContradiction.log_actualRowCount_div_tendsto_zero d
  have hconst := OAI.PiExponent.DeterminantContradiction.const_div_tendsto_zero
    (Real.log 2 / 4 - Real.log (1 - OAI.PiExponent.Collision.collisionRatio))
  simpa only [add_div, sub_div, add_sub_assoc, add_zero] using hlog.add hconst
