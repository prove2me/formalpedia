-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_coefficient_composition_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:15:13.746255+00:00
-- url     : https://prove2.me/submissions/aa61bf99-e1de-4d64-9093-bb74e5377149

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coefficient_product_pow_le_choose
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choose_le_two_pow

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → PowerSeries ℂ) (e : σ → ℕ) (k : ℕ)
    (hτc : ∀ i n, ‖PowerSeries.coeff n (τ i)‖ ≤ 1) :
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
      Real.exp (Real.log 2 * (k : ℝ)) * (2 : ℝ) ^ (∑ i, e i) := by
  have hcoeff := OAI.PiExponent.LiteralAnalytic.coefficient_product_pow_le_choose τ e k hτc
  have hchoose := OAI.PiExponent.LiteralAnalytic.choose_le_two_pow k (∑ i, e i)
  have hexp : Real.exp (Real.log 2 * (k : ℝ)) = (2 : ℝ) ^ k := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (2 : ℝ) > 0)]
  calc
    ‖PowerSeries.coeff k (∏ i, τ i ^ (e i : ℕ))‖ ≤
        (Nat.choose (k + ∑ i, e i) k : ℝ) := hcoeff
    _ ≤ (2 : ℝ) ^ (k + ∑ i, e i) := hchoose
    _ = Real.exp (Real.log 2 * (k : ℝ)) * (2 : ℝ) ^ (∑ i, e i) := by
      rw [pow_add, ← hexp]