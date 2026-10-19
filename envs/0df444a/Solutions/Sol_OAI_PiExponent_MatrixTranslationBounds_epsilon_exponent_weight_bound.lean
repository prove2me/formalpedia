-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:41:03.329001+00:00
-- url     : https://prove2.me/submissions/afce4a6f-3877-43a6-8b53-00b28bc4c268

import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_epsilon_exponent_weight_bound_coordinate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-!
Assembly of the already-proved coordinate epsilon bound.
The sum-to-weight step rewrites the remaining sum-of-products equality
explicitly, avoiding the residual sum-distribution goal in the older CE.
-/
theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ)
    (C ν ws : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws)
    (hw : ∀ i, ws ≤ w i) :
    (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) ≤
      -ν * (OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => a i) -
        OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => (d i).val) +
        C * OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => a i) / ws := by
  have hsum :
      (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) ≤
        ∑ i, (-ν * (w i * ((a i : ℝ) - (β i : ℝ))) +
          ν * (w i * ((d i).val : ℝ)) + C * (w i * (a i : ℝ)) / ws) := by
    apply Finset.sum_le_sum
    intro i hi
    exact OAI.PiExponent.MatrixTranslationBounds.epsilon_exponent_weight_bound_coordinate
      (β i) (a i) (d i) (w i) C ν ws hC hν hws (hw i)
  calc
    (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) ≤
        ∑ i, (-ν * (w i * ((a i : ℝ) - (β i : ℝ))) +
          ν * (w i * ((d i).val : ℝ)) + C * (w i * (a i : ℝ)) / ws) := hsum
    _ = -ν * (OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => a i) -
          OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => β i)) +
        ν * OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => (d i).val) +
        C * OAI.PiExponent.MatrixTranslationBounds.weight w (fun i => a i) / ws := by
      simp [OAI.PiExponent.MatrixTranslationBounds.weight,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_div]
      all_goals simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      all_goals simp only [mul_sub, Finset.sum_sub_distrib]
