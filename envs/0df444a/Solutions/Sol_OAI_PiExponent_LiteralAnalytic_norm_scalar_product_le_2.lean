-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T08:59:39.728386+00:00
-- url     : https://prove2.me/submissions/becb27a4-0470-4edf-97b9-af8ca0a6a92a

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceScalar_le
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_sum_rowWeight_eq
import Mathlib.Algebra.BigOperators.Ring.Finset
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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) - (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  rw [norm_prod]
  apply (Finset.prod_le_prod (fun r _ => norm_nonneg _)
    (fun r _ => norm_choiceScalar_le d hnu r (f r))).trans
  rw [← Real.exp_sum]
  apply le_of_eq
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_rowWeight_eq d hH]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
  ring_nf
