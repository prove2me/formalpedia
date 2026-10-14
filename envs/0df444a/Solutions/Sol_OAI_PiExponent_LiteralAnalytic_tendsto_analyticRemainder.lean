-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.tendsto_analyticRemainder
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T15:15:25.357238+00:00
-- url     : https://prove2.me/submissions/e6449736-0a0a-4f07-9d3f-ca2fabb9b5db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_tendsto_collisionRemainder
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_tendsto_translationLogTerm

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have h₁ := OAI.PiExponent.LiteralAnalytic.tendsto_collisionRemainder d
  have h₂ := OAI.PiExponent.LiteralAnalytic.tendsto_translationLogTerm d
  change Tendsto (fun H : ℝ =>
    Collision.collisionRemainder (actualRowCount d H) H +
      Real.log (translationTermCount d.m d.v0 H : ℝ) / H) atTop (𝓝 0)
  simpa using h₁.add h₂
