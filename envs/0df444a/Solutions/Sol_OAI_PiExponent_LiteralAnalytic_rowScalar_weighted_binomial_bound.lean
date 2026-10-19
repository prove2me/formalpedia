-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:56:18.950431+00:00
-- url     : https://prove2.me/submissions/bd3e6a74-f265-4125-9339-26f61991f2ec

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_rowScalar_weighted_binomial_bound_single
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (a β : σ →₀ ℕ) (e : ∀ i, Fin (a i - β i + 1)) :
    ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i) : ℕ) : ℝ) *
      (2 : ℝ) ^ (∑ i, (e i : ℕ)) ≤
        Real.exp (Real.log 4 * (∑ i, (a i : ℝ))) := by
  have hprod :
      (∏ i, (((a i).choose (β i) * (a i - β i).choose (e i : ℕ) : ℕ) : ℝ) *
        (2 : ℝ) ^ (e i : ℕ)) ≤
        ∏ i, (4 : ℝ) ^ (a i) := by
    apply Finset.prod_le_prod
    · intro i hi
      positivity
    · intro i hi
      exact OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound_single
        (a i) (β i) (e i)
  have hleft :
      ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i : ℕ) : ℕ) : ℝ) *
          (2 : ℝ) ^ (∑ i, (e i : ℕ)) =
        ∏ i, (((a i).choose (β i) * (a i - β i).choose (e i : ℕ) : ℕ) : ℝ) *
          (2 : ℝ) ^ (e i : ℕ) := by
    rw [Nat.cast_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  have hpow :
      Real.exp (Real.log 4 * (∑ i, (a i : ℝ))) =
        (4 : ℝ) ^ (∑ i, a i) := by
    have hs : (∑ i, (a i : ℝ)) = (↑(∑ i, a i) : ℝ) := by simp
    rw [hs, mul_comm (Real.log 4) (↑(∑ i, a i) : ℝ), Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  calc
    ((∏ i, (a i).choose (β i) * (a i - β i).choose (e i : ℕ) : ℕ) : ℝ) *
        (2 : ℝ) ^ (∑ i, (e i : ℕ)) =
      ∏ i, (((a i).choose (β i) * (a i - β i).choose (e i : ℕ) : ℕ) : ℝ) *
        (2 : ℝ) ^ (e i : ℕ) := hleft
    _ ≤ ∏ i, (4 : ℝ) ^ (a i) := hprod
    _ = (4 : ℝ) ^ (∑ i, a i) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = Real.exp (Real.log 4 * (∑ i, (a i : ℝ))) := hpow.symm
