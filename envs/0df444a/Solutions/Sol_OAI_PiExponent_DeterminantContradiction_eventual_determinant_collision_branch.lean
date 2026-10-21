-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventual_determinant_collision_branch
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:40:12.592986+00:00
-- url     : https://prove2.me/submissions/5b3a4222-98c1-4895-a61b-765bfe9ca95c

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_analytic_plus_arithmetic_error_lt_half
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_analytic_remainder_lt_quarter
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_actual_mean_nonneg
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_collision_rate_gt_seven_quarters

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) :
    ∀ᶠ H : ℝ in atTop,
      d.analyticError + analyticRemainder d H + (-collisionRate d H) <
        -(1 - actualMean d H) - d.arithmeticError := by
  have hbudget :=
    OAI.PiExponent.DeterminantContradiction.analytic_plus_arithmetic_error_lt_half d
  filter_upwards
    [OAI.PiExponent.DeterminantContradiction.eventual_analytic_remainder_lt_quarter d,
      OAI.PiExponent.DeterminantContradiction.eventual_actual_mean_nonneg d,
      OAI.PiExponent.DeterminantContradiction.eventual_collision_rate_gt_seven_quarters d]
    with H hrem hmean hcollision
  nlinarith [hbudget]