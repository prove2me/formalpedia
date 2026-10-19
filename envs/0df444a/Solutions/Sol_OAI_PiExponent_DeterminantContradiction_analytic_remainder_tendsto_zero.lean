-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.analytic_remainder_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:32:22.442143+00:00
-- url     : https://prove2.me/submissions/843fb4b4-d526-4d75-a379-6c25d36104f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collision_remainder_tendsto_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_remainder_tendsto_zero

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => analyticRemainder d H) atTop (𝓝 0) := by
  have h_collision : Tendsto
      (fun H : ℝ => OAI.PiExponent.Collision.collisionRemainder
        (actualRowCount d H) H) atTop (𝓝 0) :=
    OAI.PiExponent.DeterminantContradiction.collision_remainder_tendsto_zero d
  have h_translation : Tendsto
      (fun H : ℝ => Real.log (translationTermCount d.m d.v0 H : ℝ) / H)
      atTop (𝓝 0) :=
    OAI.PiExponent.DeterminantContradiction.translation_remainder_tendsto_zero d
  simpa [OAI.PiExponent.LiteralAnalytic.analyticRemainder] using
    h_collision.add h_translation
