-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_determinant_budget_gap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:18:39.020567+00:00
-- url     : https://prove2.me/submissions/117ebed5-9281-41c9-b6ee-99a75cca2a42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_determinant_collision_branch
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_determinant_exponent_branch

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) :
    ∀ᶠ H : ℝ in atTop,
      d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) <
        -(1 - actualMean d H) - d.arithmeticError := by
  have hcollision :=
    OAI.PiExponent.DeterminantContradiction.eventual_determinant_collision_branch d hnu
  have hexponent :=
    OAI.PiExponent.DeterminantContradiction.eventual_determinant_exponent_branch d hnu
  filter_upwards [hcollision.and hexponent] with H h
  rw [add_max]
  exact max_lt h.1 h.2