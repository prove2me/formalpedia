-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le_of_permutation_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T10:35:30.181887+00:00
-- url     : https://prove2.me/submissions/1c40d115-abae-4c82-b162-3e1d139f1a40
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
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weighted_choiceMatrix_permanent_collision_bound
import Theorems.Thm_OAI_PiExponent_finite_permutation_card_le_exp_card_log

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    (∑ σ : Equiv.Perm (Row d H), ∏ r : Row d H,
        ‖choiceMatrix d selection f r (σ r)‖) ≤
      Real.exp
        (-(Real.log 2 / 4) *
          (∑ A : Transverse d H,
            (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
          (actualRowCount d H : ℝ) *
            (H * d.holomorphicError + Real.log (actualRowCount d H : ℝ) +
              Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio))) := by
  have hp := OAI.PiExponent.LiteralAnalytic.weighted_choiceMatrix_permanent_collision_bound
    d hH selection f
  have hc := OAI.PiExponent.finite_permutation_card_le_exp_card_log
    (α := Row d H)
  have hmul := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ Real.exp
      (-(Real.log 2 / 4) *
        (∑ A : Transverse d H,
          (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) *
          (H * d.holomorphicError + Real.log 2 / 4 -
            Real.log (1 - Collision.collisionRatio))) from
      (Real.exp_pos _).le)
  rw [show (Fintype.card (Row d H) : ℝ) = (actualRowCount d H : ℝ) by rfl] at hmul
  calc
    (∑ σ : Equiv.Perm (Row d H), ∏ r : Row d H,
        ‖choiceMatrix d selection f r (σ r)‖) ≤
        (Fintype.card (Equiv.Perm (Row d H)) : ℝ) *
          Real.exp
            (-(Real.log 2 / 4) *
              (∑ A : Transverse d H,
                (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
              (actualRowCount d H : ℝ) *
                (H * d.holomorphicError + Real.log 2 / 4 -
                  Real.log (1 - Collision.collisionRatio))) := hp
    _ ≤ Real.exp ((actualRowCount d H : ℝ) * Real.log (actualRowCount d H : ℝ)) *
          Real.exp
            (-(Real.log 2 / 4) *
              (∑ A : Transverse d H,
                (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
              (actualRowCount d H : ℝ) *
                (H * d.holomorphicError + Real.log 2 / 4 -
                  Real.log (1 - Collision.collisionRatio))) := hmul
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
