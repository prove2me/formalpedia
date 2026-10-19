-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.norm_choiceScalar_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T11:51:43.802732+00:00
-- url     : https://prove2.me/submissions/4bbcdbb1-41f7-4438-8871-fd9696af4760

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceScalar_factorized_estimate
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceScalar_weight_identity

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * d.translationError) := by
  have ha := OAI.PiExponent.LiteralAnalytic.choiceScalar_factorized_estimate d hnu r t
  have hw := OAI.PiExponent.LiteralAnalytic.choiceScalar_weight_identity d r t
  rw [hw] at ha
  calc
    ‖choiceScalar d r t‖ ≤
        Real.exp (H * d.translationError) *
          Real.exp (-nu * (indexWeight d t.1 - rowWeight d r)) := ha
    _ = Real.exp
        (-nu * (indexWeight d t.1 - rowWeight d r) + H * d.translationError) := by
          rw [← Real.exp_add]
          congr 1
          ring