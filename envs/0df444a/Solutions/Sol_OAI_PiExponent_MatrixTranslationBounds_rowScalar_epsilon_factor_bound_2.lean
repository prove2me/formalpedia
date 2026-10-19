-- Prove2me | solution 2 for OAI.PiExponent.MatrixTranslationBounds.rowScalar_epsilon_factor_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:41:08.738554+00:00
-- url     : https://prove2.me/submissions/f37b2f6b-eb47-48d1-8bb7-69ee8a36c131

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_product_exp_bound
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_exponent_weight_bound_coordinate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.MatrixTranslationBounds OAI.PiExponent.RowTranslation

/-! Direct epsilon factor estimate with only established prerequisite lemmas. -/

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖∏ i, ε i ^ (a i - β i - d i)‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        C * weight w (fun i => a i) / ws) := by
  have hprod := OAI.PiExponent.MatrixTranslationBounds.epsilon_product_exp_bound
    ε β a d w C ν hε
  have hsum :
      (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) ≤
        ∑ i, (-ν * (w i * ((a i : ℝ) - (β i : ℝ))) +
          ν * (w i * ((d i).val : ℝ)) + C * (w i * (a i : ℝ)) / ws) := by
    apply Finset.sum_le_sum
    intro i hi
    exact OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound_coordinate
      (β i) (a i) (d i) (w i) C ν ws hC hν hws (hw i)
  have hexp :
      (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) ≤
      -ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        ν * weight w (fun i => (d i).val) +
        C * weight w (fun i => a i) / ws := by
    calc
      _ ≤ ∑ i, (-ν * (w i * ((a i : ℝ) - (β i : ℝ))) +
          ν * (w i * ((d i).val : ℝ)) + C * (w i * (a i : ℝ)) / ws) := hsum
      _ = _ := by
        simp [weight, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
        all_goals simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
        all_goals simp only [mul_sub, Finset.sum_sub_distrib]
  exact le_trans hprod (Real.exp_le_exp.mpr hexp)
