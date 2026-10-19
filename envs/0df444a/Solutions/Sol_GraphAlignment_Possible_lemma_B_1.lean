-- Prove2me | solution 1 for GraphAlignment.Possible.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:20:41.409988+00:00
-- url     : https://prove2.me/submissions/1932b969-a7d7-44a1-b01c-08f2d84c4773

import Mathlib
set_option autoImplicit false

theorem solution (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (α ^ k + β ^ k) ^ ((n : ℝ) / k) ≤ (α ^ 2 + β ^ 2) ^ ((n : ℝ) / 2) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hp : (1 : ℝ) ≤ (k : ℝ) / 2 := by rw [le_div_iff₀ (by norm_num)]; linarith
  have h1 : α ^ k + β ^ k ≤ (α ^ 2 + β ^ 2) ^ ((k : ℝ) / 2) := by
    have key := Real.add_rpow_le_rpow_add (sq_nonneg α) (sq_nonneg β) hp
    have ea : (α ^ 2) ^ ((k : ℝ) / 2) = α ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hα.le]
      have : (2 : ℕ) * ((k : ℝ) / 2) = k := by push_cast; ring
      rw [this, Real.rpow_natCast]
    have eb : (β ^ 2) ^ ((k : ℝ) / 2) = β ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
      have : (2 : ℕ) * ((k : ℝ) / 2) = k := by push_cast; ring
      rw [this, Real.rpow_natCast]
    rw [ea, eb] at key
    exact key
  have hn : (0 : ℝ) ≤ (n : ℝ) / k := by positivity
  calc (α ^ k + β ^ k) ^ ((n : ℝ) / k)
      ≤ ((α ^ 2 + β ^ 2) ^ ((k : ℝ) / 2)) ^ ((n : ℝ) / k) :=
        Real.rpow_le_rpow (by positivity) h1 hn
    _ = (α ^ 2 + β ^ 2) ^ ((n : ℝ) / 2) := by
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        field_simp
