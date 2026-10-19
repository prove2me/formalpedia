-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.choiceMatrix_permutation_term_collision_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:07:43.217923+00:00
-- url     : https://prove2.me/submissions/2e649b77-5bee-475b-a280-3175c3c4c69a
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
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_cofinal_nonzero_actual_minors
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_arithmetic_lower_estimate
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_determinant_analytic_estimate
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_determinant_budget_gap

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

-- The strict base-parameter inequalities exclude nu <= 2.
private theorem parameters_two_lt_nu {nu : ℝ} (p : Parameters nu) : 2 < nu := by
  have hC : 0 < (p.C : ℝ) := lt_trans zero_lt_one p.one_lt_C
  have hB : 0 < (p.B : ℝ) :=
    p.theta_pos.trans (p.theta_lt_A.trans p.A_lt_B)
  have hBC : (p.B : ℝ) * (p.C : ℝ) < 1 :=
    (lt_div_iff₀ hC).mp p.B_lt_inv_C
  have hBB : (p.B : ℝ) ^ 2 < (p.theta : ℝ) := by
    have h₁ := mul_lt_mul_of_pos_left p.B_lt_C_theta hB
    have h₂ := mul_lt_mul_of_pos_right hBC p.theta_pos
    nlinarith
  have hgap : 2 * ((p.A : ℝ) - p.theta) < 1 - p.theta := by
    nlinarith [sq_nonneg ((p.B : ℝ) - 1), p.A_lt_B]
  by_contra hn
  have hn' : nu ≤ 2 := le_of_not_gt hn
  have hdiff : 0 < (p.A : ℝ) - p.theta := sub_pos.mpr p.theta_lt_A
  have hm := mul_le_mul_of_nonneg_right hn' hdiff.le
  linarith [p.approximation_gap]

-- This reduction uses determinant cancellation throughout. It never assumes
-- the pointwise choice-matrix estimate that is being asked for.
private theorem fixedData_false_from_determinant_estimates
    {nu : ℝ} (d : FixedData nu) : False := by
  have hnu : 2 < nu := parameters_two_lt_nu d.base
  have hgap := eventual_determinant_budget_gap d hnu
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hgap
  obtain ⟨T, hLT, hT, selection, hdet⟩ :=
    cofinal_nonzero_actual_minors d hnu L
  have hlower :=
    actual_minor_arithmetic_lower_estimate d T hT selection hdet
  have hupper :=
    actual_minor_determinant_analytic_estimate d (by linarith : 0 ≤ nu)
      hT selection hdet
  exact (not_le_of_gt (hL T hLT)) (hlower.trans hupper)

-- Sanity check of the abandoned entrywise route:
-- choose every selected column and every transverse index equal to zero,
-- and choose the subtraction order equal to the row order. RowChoices permits
-- these choices even when beta is nonzero, because subtraction is in Nat.
-- The choice matrix is all ones, its permutation products are one, and its
-- collision sum is the square of the row count. A determinant estimate does
-- not imply the desired entrywise estimate. The children instead rule out
-- FixedData via actual minors, proving the target by elimination of d.
theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H)
    (σ : Equiv.Perm (Row d H)) :
    (∏ r : Row d H, ‖choiceMatrix d selection f r (σ r)‖) ≤
      Real.exp
        (-(Real.log 2 / 4) *
          (∑ A : Transverse d H,
            (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
          (actualRowCount d H : ℝ) *
            (H * d.holomorphicError + Real.log 2 / 4 -
              Real.log (1 - Collision.collisionRatio))) := by
  exact (fixedData_false_from_determinant_estimates d).elim