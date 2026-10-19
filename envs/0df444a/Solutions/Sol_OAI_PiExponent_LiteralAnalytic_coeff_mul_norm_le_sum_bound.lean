-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.coeff_mul_norm_le_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:45:01.417993+00:00
-- url     : https://prove2.me/submissions/839ff419-eb45-47a5-b24d-bce8323bdca8

import Mathlib
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Order

open scoped BigOperators
theorem solution
    (f g : PowerSeries ℂ) (a : ℕ → ℝ) (B : ℝ) (n : ℕ)
    (hB : 0 ≤ B)
    (hf : ∀ r, ‖PowerSeries.coeff r f‖ ≤ a r)
    (hg : ∀ r, ‖PowerSeries.coeff r g‖ ≤ B) :
    ‖PowerSeries.coeff n (f * g)‖ ≤
      B * ∑ r ∈ Finset.range (n + 1), a r := by
  rw [PowerSeries.coeff_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun p : ℕ × ℕ => a p.1 * B) (fun p _ => ?_)).trans (le_of_eq ?_))
  · rw [norm_mul]; exact mul_le_mul (hf _) (hg _) (norm_nonneg _) ((norm_nonneg _).trans (hf _))
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _; ring
