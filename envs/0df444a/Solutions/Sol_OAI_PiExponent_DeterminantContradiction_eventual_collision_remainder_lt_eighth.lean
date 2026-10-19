-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_collision_remainder_lt_eighth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:08:41.270645+00:00
-- url     : https://prove2.me/submissions/30c1691d-3d72-4471-b033-829e196f4ca8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collision_log_row_count_div_tendsto_zero
import Mathlib.Topology.Algebra.Order.Field

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∀ᶠ H : ℝ in atTop,
      Collision.collisionRemainder (actualRowCount d H) H < 1 / 8 := by
  have hcount :=
    OAI.PiExponent.DeterminantContradiction.collision_log_row_count_div_tendsto_zero d
  have htwo : Tendsto (fun H : ℝ => (Real.log 2 / 4) / H)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hratio : Tendsto (fun H : ℝ => Real.log (1 - Collision.collisionRatio) / H)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto
      (fun H : ℝ => Collision.collisionRemainder (actualRowCount d H) H)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Collision.collisionRemainder, add_div, sub_div, add_zero, sub_zero]
      using (hcount.add htwo).sub hratio
  exact hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))