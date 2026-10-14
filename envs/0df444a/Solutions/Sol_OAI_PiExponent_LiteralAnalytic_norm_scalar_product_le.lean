-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.norm_scalar_product_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T12:52:03.676476+00:00
-- url     : https://prove2.me/submissions/9b83a3d8-1db9-4e74-94c7-69c6535c3445
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceScalar_norm_le_of_weight
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowWeight_sum_eq_actualMean

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

set_option maxHeartbeats 600000

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (f : ChoiceFamily d H) :
    ‖∏ r, choiceScalar d r (f r)‖ ≤ Real.exp
      (-nu * ((∑ r, indexWeight d (f r).1) -
          (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  classical
  have hrow (r : Row d H) :
      ‖choiceScalar d r (f r)‖ ≤ Real.exp
        (-nu * (indexWeight d (f r).1 - rowWeight d r) + H * d.translationError) :=
    OAI.PiExponent.LiteralAnalytic.choiceScalar_norm_le_of_weight d hnu hH r (f r)
  have hsum : (∑ r : Row d H, rowWeight d r) =
      (actualRowCount d H : ℝ) * H * actualMean d H :=
    OAI.PiExponent.LiteralAnalytic.rowWeight_sum_eq_actualMean d hH
  calc
    ‖∏ r : Row d H, choiceScalar d r (f r)‖ =
        ∏ r : Row d H, ‖choiceScalar d r (f r)‖ := Complex.norm_prod _ _
    _ ≤ ∏ r : Row d H,
        Real.exp (-nu * (indexWeight d (f r).1 - rowWeight d r) +
          H * d.translationError) := by
      apply Finset.prod_le_prod
      · intro r hr
        exact norm_nonneg _
      · intro r hr
        exact hrow r
    _ = Real.exp (∑ r : Row d H,
        (-nu * (indexWeight d (f r).1 - rowWeight d r) +
          H * d.translationError)) := by
      rw [← Real.exp_sum]
    _ = Real.exp
        (-nu * ((∑ r : Row d H, indexWeight d (f r).1) -
            (actualRowCount d H : ℝ) * H * actualMean d H) +
          (actualRowCount d H : ℝ) * H * d.translationError) := by
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
      simp [actualRowCount]
      ring