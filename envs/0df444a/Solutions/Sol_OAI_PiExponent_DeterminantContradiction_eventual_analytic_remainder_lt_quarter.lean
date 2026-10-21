-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_analytic_remainder_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:45:30.092329+00:00
-- url     : https://prove2.me/submissions/5022ed9e-6952-48b2-bf4b-75f33dede841

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_collision_remainder_lt_eighth
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_translation_remainder_lt_eighth

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∀ᶠ H : ℝ in atTop, analyticRemainder d H < 1 / 4 := by
  filter_upwards
    [OAI.PiExponent.DeterminantContradiction.eventual_collision_remainder_lt_eighth d,
      OAI.PiExponent.DeterminantContradiction.eventual_translation_remainder_lt_eighth d]
    with H hcollision htranslation
  change Collision.collisionRemainder (actualRowCount d H) H +
      Real.log (translationTermCount d.m d.v0 H : ℝ) / H < 1 / 4
  linarith