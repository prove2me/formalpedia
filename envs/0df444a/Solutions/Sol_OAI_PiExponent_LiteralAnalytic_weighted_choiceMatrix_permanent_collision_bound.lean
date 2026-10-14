-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.weighted_choiceMatrix_permanent_collision_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T10:47:57.958863+00:00
-- url     : https://prove2.me/submissions/0694e56e-b45b-44cb-92f0-8514134462c8
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
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choiceMatrix_permutation_term_collision_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    (∑ σ : Equiv.Perm (Row d H), ∏ r : Row d H,
        ‖choiceMatrix d selection f r (σ r)‖) ≤
      (Fintype.card (Equiv.Perm (Row d H)) : ℝ) *
        Real.exp
          (-(Real.log 2 / 4) *
            (∑ A : Transverse d H,
              (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
            (actualRowCount d H : ℝ) *
              (H * d.holomorphicError + Real.log 2 / 4 -
                Real.log (1 - Collision.collisionRatio))) := by
  let B : ℝ := Real.exp
    (-(Real.log 2 / 4) *
      (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
      (actualRowCount d H : ℝ) *
        (H * d.holomorphicError + Real.log 2 / 4 -
          Real.log (1 - Collision.collisionRatio)))
  calc
    (∑ σ : Equiv.Perm (Row d H), ∏ r : Row d H,
        ‖choiceMatrix d selection f r (σ r)‖) ≤
        ∑ _σ : Equiv.Perm (Row d H), B := by
          apply Finset.sum_le_sum
          intro σ hσ
          exact OAI.PiExponent.LiteralAnalytic.choiceMatrix_permutation_term_collision_bound
            d hH selection f σ
    _ = (Fintype.card (Equiv.Perm (Row d H)) : ℝ) * B := by simp [B]
