-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_exp_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:53:46.260457+00:00
-- url     : https://prove2.me/submissions/dd0bbaeb-249e-46ac-8944-29ed8840fe94

import Mathlib
open scoped BigOperators

theorem solution {d m : Nat} (w : Fin d → Rat) (q : Rat) (b : Fin m → (Fin d →₀ Nat)) (a : Fin d →₀ Nat) (hsum : (∑ i, b i) = a) (hb : ∀ i, ∑ k, (w k : Real) * ((b i) k : Real) ≤ (q : Real)) : ∑ k, (w k : Real) * (a k : Real) ≤ ((q * (m : Rat) : Rat) : Real) := by
  subst hsum
  have : ∑ k, (w k : Real) * (((∑ i, b i) k : ℕ) : Real) = ∑ i, ∑ k, (w k : Real) * ((b i) k : Real) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.finset_sum_apply, Nat.cast_sum, Finset.mul_sum]
  rw [this]
  calc _ ≤ ∑ _i : Fin m, (q : Real) := Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp [mul_comm]
