-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.epsilon_product_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:38:10.644818+00:00
-- url     : https://prove2.me/submissions/9edb8b85-e16d-496e-a715-22eed37bb213

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators Topology

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (C ν : ℝ)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖∏ i, ε i ^ (a i - β i - d i)‖ ≤
      Real.exp (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) := by
  rw [Complex.norm_prod]
  calc
    (∏ i, ‖ε i ^ (a i - β i - d i)‖) ≤
        ∏ i, Real.exp
          (((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        rw [norm_pow]
        calc
          ‖ε i‖ ^ (a i - β i - d i) ≤
              Real.exp (C - ν * w i) ^ (a i - β i - d i) := by
            gcongr
            exact hε i
          _ = Real.exp
              (((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) := by
            rw [← Real.exp_nat_mul]
    _ = Real.exp
        (∑ i, ((a i - β i - (d i).val : ℕ) : ℝ) * (C - ν * w i)) := by
      rw [← Real.exp_sum]
