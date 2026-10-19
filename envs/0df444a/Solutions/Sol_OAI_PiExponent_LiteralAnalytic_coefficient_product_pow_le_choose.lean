-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T16:33:47.689317+00:00
-- url     : https://prove2.me/submissions/09834f26-238d-419c-acf8-7d694578a9b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coefficient_product_pow_le_choose_weighted

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (e : σ → ℕ) (k : ℕ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  simpa using
    OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose_weighted
      (τ := τ) (e := e) (k := k) (C := fun _ => (1 : ℝ)) hτc
