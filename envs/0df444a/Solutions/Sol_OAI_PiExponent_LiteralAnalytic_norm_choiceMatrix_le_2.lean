-- Prove2me | solution 2 for OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T07:42:51.374649+00:00
-- url     : https://prove2.me/submissions/d58e1e1d-8af0-40e6-be42-aec2d708d50e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le_of_permutation_sum
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_det_le_permutation_sum
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
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

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  classical
  calc
    ‖(choiceMatrix d selection f).det‖ ≤
        ∑ s : Equiv.Perm (Row d H), ∏ r : Row d H,
          ‖choiceMatrix d selection f r (s r)‖ :=
      norm_det_le_permutation_sum (choiceMatrix d selection f)
    _ ≤ Real.exp
        (-(Real.log 2 / 4) *
          (∑ A : Transverse d H,
            (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
          (actualRowCount d H : ℝ) *
            (H * d.holomorphicError + Real.log (actualRowCount d H : ℝ) +
              Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio))) :=
      norm_choiceMatrix_le_of_permutation_sum d hH selection f
    _ = _ := by
      congr 1
      unfold Collision.collisionRemainder
      field_simp [ne_of_gt hH]
      ring
