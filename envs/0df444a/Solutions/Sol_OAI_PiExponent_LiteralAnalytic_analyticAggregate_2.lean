-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.analyticAggregate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T07:47:30.690638+00:00
-- url     : https://prove2.me/submissions/0590a2c3-7327-4526-83d6-e5e43087fa0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_tendsto_analyticRemainder
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Mathlib.Tactic
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution : AnalyticAggregateStatement := by
  intro nu hnu d
  refine ⟨analyticRemainder d, tendsto_analyticRemainder d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hne
  exact actual_minor_analytic_bound d (by linarith) hH selection hne
