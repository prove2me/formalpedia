-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_grid_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:32:29.021566+00:00
-- url     : https://prove2.me/submissions/06ac23ff-ef55-4c77-80e0-c9839159e699

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- The squared stopped-cell increment is bounded by full-cell energy and a crossing allowance. -/
theorem solution (X : NNReal → ℝ) (u : ℕ → NNReal) (hu : Monotone u)
    (n : ℕ) (t R : NNReal)
    (hX : ∀ a b : NNReal, a ≤ t → b ≤ t → |X a - X b| ≤ (R : ℝ)) :
    let S := (Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))
    ∀ k ∈ Finset.range n,
      (X (min t (u (k+1))) - X (min t (u k)))^2 ≤
        (X (u (k+1)) - X (u k))^2 + (if k ∈ S then (R : ℝ)^2 else 0) := by
  classical
  intro S k hk
  by_cases h1 : u (k+1) ≤ t
  · rw [min_eq_right h1,min_eq_right ((hu (Nat.le_succ k)).trans h1)]
    exact le_add_of_nonneg_right (by split <;> positivity)
  by_cases h2 : t ≤ u k
  · rw [min_eq_left h2,min_eq_left (h2.trans (hu (Nat.le_succ k))),sub_self,zero_pow (by decide)]
    positivity
  have hs : k ∈ S := Finset.mem_filter.mpr ⟨hk,lt_of_not_ge h2,lt_of_not_ge h1⟩
  rw [if_pos hs]
  have hsq : (X (min t (u (k+1))) - X (min t (u k)))^2 ≤ (R : ℝ)^2 := by
    have h := hX (min t (u (k+1))) (min t (u k)) (min_le_left _ _) (min_le_left _ _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith [sq_nonneg (X (u (k+1)) - X (u k))]
