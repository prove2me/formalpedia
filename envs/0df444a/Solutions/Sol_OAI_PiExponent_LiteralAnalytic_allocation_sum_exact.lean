-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.allocation_sum_exact
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:01:16.051154+00:00
-- url     : https://prove2.me/submissions/b3109a09-21b2-4264-a864-e56ec2ffdacc

import Mathlib.Tactic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_allocation_sum_exact_nat

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    (∑ n : σ → Fin (k + 1),
      (if ∑ i, (n i : ℕ) = k then
        ∏ i,
          (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
           else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ))
       else 0)) =
      (if ∑ i, e i = 0 then (if k = 0 then (1 : ℝ) else 0)
       else (Nat.choose (k + (∑ i, e i) - 1) k : ℝ)) := by
  exact_mod_cast OAI.PiExponent.LiteralAnalytic.allocation_sum_exact_nat e k