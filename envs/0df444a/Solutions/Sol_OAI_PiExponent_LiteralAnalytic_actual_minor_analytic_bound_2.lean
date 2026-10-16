-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T07:46:02.298867+00:00
-- url     : https://prove2.me/submissions/5a5a0d97-30e9-4483-b56c-584db8c50da8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_actual_summand_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_card_choiceFamily_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_expansion
import Theorems.Thm_OAI_PiExponent_DeterminantAnalyticBound_log_norm_sum_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_pos
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < translationTermCount d.m d.v0 H := by
    unfold translationTermCount
    positivity
  have hc : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (translationTermCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast card_choiceFamily_le d H
  have hb := DeterminantAnalyticBound.log_norm_sum_le
    (fun f : ChoiceFamily d H =>
      (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det)
    (actualMinor d H selection).det (actualRowCount_pos d hH) hH hQ hc
    (actual_minor_expansion d selection) hne (norm_actual_summand_le d hnu hH selection)
  convert! hb using 1
  unfold analyticRemainder
  ring
