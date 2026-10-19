-- Prove2me | solution 1 for NesterovRCD.Accelerated.trivial_ineq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:36:28.642247+00:00
-- url     : https://prove2.me/submissions/8a4855e1-7d32-4eea-b485-6ffccf13a362

import Mathlib
set_option autoImplicit false

theorem solution :
    (∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, 2 * (k : ℝ) * t ≤ (1 + t) ^ k - (1 - t) ^ k) ∧
    (∀ n : ℕ, 0 < n → ∀ σ : ℝ, 0 ≤ σ → ∀ k : ℕ,
      ((k : ℝ) + 1) / n * Real.sqrt σ
        ≤ (1 + Real.sqrt σ / (2 * n)) ^ (k + 1) - (1 - Real.sqrt σ / (2 * n)) ^ (k + 1)) := by
  have h1 : ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, 2 * (k : ℝ) * t ≤ (1 + t) ^ k - (1 - t) ^ k := by
    intro t ht k
    have key : ∀ k : ℕ, 2 * (k : ℝ) * t ≤ (1 + t) ^ k - (1 - t) ^ k ∧
        2 ≤ (1 + t) ^ k + (1 - t) ^ k := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        obtain ⟨ha, hb⟩ := ih
        have e1 : (1 + t) ^ (k+1) - (1 - t) ^ (k+1)
            = ((1 + t) ^ k - (1 - t) ^ k) + t * ((1 + t) ^ k + (1 - t) ^ k) := by ring
        have e2 : (1 + t) ^ (k+1) + (1 - t) ^ (k+1)
            = ((1 + t) ^ k + (1 - t) ^ k) + t * ((1 + t) ^ k - (1 - t) ^ k) := by ring
        have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
        constructor
        · rw [e1]; push_cast; nlinarith [mul_le_mul_of_nonneg_left hb ht]
        · rw [e2]
          have : 0 ≤ t * ((1 + t) ^ k - (1 - t) ^ k) :=
            mul_nonneg ht (le_trans (by positivity) ha)
          linarith
    exact (key k).1
  refine ⟨h1, ?_⟩
  intro n hn σ hσ k
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have ht : 0 ≤ Real.sqrt σ / (2 * n) := by positivity
  have := h1 _ ht (k + 1)
  have e : ((k : ℝ) + 1) / n * Real.sqrt σ = 2 * ((k + 1 : ℕ) : ℝ) * (Real.sqrt σ / (2 * n)) := by
    push_cast; field_simp
  rw [e]; exact this
