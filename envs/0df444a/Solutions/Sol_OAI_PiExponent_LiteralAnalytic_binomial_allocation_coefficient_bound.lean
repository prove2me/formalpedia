-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.binomial_allocation_coefficient_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:56:09.934986+00:00
-- url     : https://prove2.me/submissions/8a0e8bf7-f7ea-4687-b9eb-c96c74320f41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_exact

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i,
          (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
           else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ))
       else 0)) ≤ (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  rw [OAI.PiExponent.LiteralAnalytic.allocation_sum_exact e k]
  by_cases hE : (∑ i, e i) = 0
  · by_cases hk : k = 0 <;> simp [hE, hk]
  · rw [if_neg hE]
    exact_mod_cast
      (Nat.choose_le_choose k (Nat.sub_le (k + ∑ i, e i) 1))
