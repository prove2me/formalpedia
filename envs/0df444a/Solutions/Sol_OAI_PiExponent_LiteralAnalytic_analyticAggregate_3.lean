-- Prove2me | solution 3 for OAI.PiExponent.LiteralAnalytic.analyticAggregate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T12:16:18.83115+00:00
-- url     : https://prove2.me/submissions/551c7cac-e10b-4360-9b1c-a11c5731164c

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_tendsto_analyticRemainder
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution : AnalyticAggregateStatement := by
  intro nu hnu d
  refine ⟨LiteralAnalytic.analyticRemainder d,
    LiteralAnalytic.tendsto_analyticRemainder d, ?_⟩
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hne
  exact LiteralAnalytic.actual_minor_analytic_bound d (by linarith) hH selection hne
