-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.weighted_binomial_allocation_le_choose
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:35:56.529928+00:00
-- url     : https://prove2.me/submissions/e5638332-f666-4394-87db-f79dd969f013
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_binomial_allocation_coefficient_bound

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (A : σ → ℝ) (k : ℕ)
    (hA : ∀ i, 0 ≤ A i) :
    ∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i, (A i *
          (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
           else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ)))
       else 0) ≤
      (∏ i, A i) * (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  have hfactor :
      (∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i : ℕ) = k then
          ∏ i, (A i *
            (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
             else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ)))
         else 0)) =
      (∏ i, A i) *
        (∑ n : σ → Fin (k + 1),
          (if ∑ i, (n i : ℕ) = k then
            ∏ i,
              (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
               else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ))
           else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : ∑ i, (n i : ℕ) = k
    · simp only [if_pos h, Finset.prod_mul_distrib]
    · simp [h]
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left
    (OAI.PiExponent.LiteralAnalytic.binomial_allocation_coefficient_bound e k)
    (Finset.prod_nonneg fun i hi => hA i)
