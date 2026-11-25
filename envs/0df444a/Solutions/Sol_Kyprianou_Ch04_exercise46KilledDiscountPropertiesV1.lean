-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46KilledDiscountPropertiesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:28:26.784492+00:00
-- url     : https://prove2.me/submissions/3219082c-a905-4cba-a019-4e971d05f824

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Measurable bounded killed Laplace payoff is strictly decreasing at a positive rate. -/
theorem solution
    (beta : Real) (hb : 0 ≤ beta) :
    let d : WithTop NNReal → Real := fun z =>
      if z = ⊤ then 0 else Real.exp (-beta * (((z.untopD 0 : NNReal) : Real)))
    Measurable d ∧ (∀ z, 0 ≤ d z ∧ d z ≤ 1) ∧
      (0 < beta → StrictAnti d) := by
  dsimp only
  classical
  refine ⟨?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_singleton (⊤ : WithTop NNReal))
      measurable_const (Real.measurable_exp.comp (measurable_const.mul
        (measurable_coe_nnreal_real.comp (WithTop.measurable_untopD 0))))
  · intro z
    by_cases hz : z = ⊤
    · simp [hz]
    · simp only [if_neg hz]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (NNReal.coe_nonneg _))⟩
  · intro h a b hab
    have ha : a ≠ ⊤ := ne_top_of_lt hab
    by_cases hbt : b = ⊤
    · simp [ha, hbt, Real.exp_pos]
    · simp only [if_neg ha, if_neg hbt]
      apply Real.exp_lt_exp.mpr
      have hh := (ENNReal.toReal_lt_toReal ha hbt).mpr hab
      exact mul_lt_mul_of_neg_left hh (neg_lt_zero.mpr h)
