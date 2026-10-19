-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_choose
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:22:54.479362+00:00
-- url     : https://prove2.me/submissions/a121c3ac-b52b-42e8-a5c4-2f5753c92cb8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_coeff_prod_norm_le_weighted_allocations
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weighted_binomial_allocation_le_choose

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → PowerSeries ℂ) (e : σ → ℕ) (A : σ → ℝ) (k : ℕ)
    (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ i n,
      ‖PowerSeries.coeff n (f i)‖ ≤
        A i *
          (if e i = 0 then (if n = 0 then (1 : ℝ) else 0)
           else (Nat.choose (n + e i - 1) n : ℝ))) :
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
      (∏ i, A i) * (Nat.choose (k + ∑ i, e i) k : ℝ) := by
  calc
    ‖PowerSeries.coeff k (∏ i, f i)‖ ≤
        ∑ n : σ → Fin (k + 1),
          (if ∑ i, (n i : ℕ) = k then
            ∏ i, (A i *
              (if e i = 0 then (if (n i : ℕ) = 0 then (1 : ℝ) else 0)
               else (Nat.choose ((n i : ℕ) + e i - 1) (n i : ℕ) : ℝ)))
           else 0) :=
      OAI.PiExponent.LiteralAnalytic.coeff_prod_norm_le_weighted_allocations
        f e A k hA hf
    _ ≤ (∏ i, A i) * (Nat.choose (k + ∑ i, e i) k : ℝ) :=
      OAI.PiExponent.LiteralAnalytic.weighted_binomial_allocation_le_choose
        e A k hA