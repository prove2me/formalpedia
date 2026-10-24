-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:38:52.757784+00:00
-- url     : https://prove2.me/submissions/9f5b0c25-0463-4ef4-a38c-f03769d6df6d

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_pow_norm_le_choose_weighted
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_prod_norm_le_weighted_choose

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (e : σ → ℕ) (k : ℕ) (C : σ → ℝ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ C i) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      (∏ i, C i ^ e i) * (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  have hC : ∀ i, 0 ≤ C i := by
    intro i
    exact le_trans (norm_nonneg _) (hτc i 0)
  have hA : ∀ i, 0 ≤ C i ^ e i := by
    intro i
    exact pow_nonneg (hC i) _
  have hpow : ∀ i n,
      ‖PowerSeries.coeff n (τ i ^ (e i : ℕ))‖ ≤
        C i ^ e i *
          (if e i = 0 then (if n = 0 then (1 : ℝ) else 0)
           else (Nat.choose (n + e i - 1) n : ℝ)) := by
    intro i n
    exact OAI.PiExponent.LiteralAnalytic.coeff_pow_norm_le_choose_weighted
      (τ i) (e i) n (C i) (hC i) (hτc i)
  exact OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_choose
    (f := fun i => τ i ^ (e i : ℕ)) (e := e) (A := fun i => C i ^ e i)
    k hA hpow