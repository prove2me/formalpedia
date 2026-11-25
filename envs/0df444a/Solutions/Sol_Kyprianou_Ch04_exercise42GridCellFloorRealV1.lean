-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42GridCellFloorRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:33:36.883644+00:00
-- url     : https://prove2.me/submissions/8ea9c4fb-d256-4f9f-a400-7fea1d305b24

import Mathlib
open Set
set_option autoImplicit false

theorem solution
    (T : ℝ) (hT : 0 < T) (n i : ℕ) (s : ℝ)
    (hs : s ∈ Set.Ico (T * (i : ℝ) / ((n : ℝ) + 2))
      (T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2))) :
    ⌊(s / T) * ((n : ℝ) + 2)⌋₊ = i := by
  have hs0 : 0 ≤ s :=
    (show 0 ≤ T * (i : ℝ) / ((n : ℝ) + 2) by positivity).trans hs.1
  have hn : 0 < (n : ℝ) + 2 := by positivity
  apply (Nat.floor_eq_iff (mul_nonneg (div_nonneg hs0 hT.le) hn.le)).2
  have h1' := (div_le_iff₀ hn).mp hs.1
  have h2' := (lt_div_iff₀ hn).mp hs.2
  rw [Nat.cast_add, Nat.cast_one] at h2'
  rw [div_mul_eq_mul_div]
  exact ⟨(le_div_iff₀ hT).mpr (by linarith [h1']),
    (div_lt_iff₀ hT).mpr (by linarith [h2'])⟩
