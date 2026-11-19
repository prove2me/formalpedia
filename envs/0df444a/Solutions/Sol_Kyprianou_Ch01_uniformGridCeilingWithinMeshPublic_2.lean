-- Prove2me | solution 2 for Kyprianou.Ch01.uniformGridCeilingWithinMeshPublic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:46:04.651661+00:00
-- url     : https://prove2.me/submissions/bfa4db99-2c90-421b-afe9-a3618a9f54e3

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem solution
    (delta t : ℝ) (hdelta : 0 < delta) (ht : 0 ≤ t) :
    ∃ n : ℕ, t ≤ (n : ℝ) * delta ∧
      (n : ℝ) * delta < t + delta := by 
  refine ⟨⌈t / delta⌉₊, ?_, ?_⟩
  · have h1 := Nat.le_ceil (t / delta)
    have := (div_le_iff₀ hdelta).1 h1
    linarith
  · have h2 := Nat.ceil_lt_add_one (div_nonneg ht hdelta.le)
    have h3 : (⌈t / delta⌉₊ : ℝ) * delta < (t / delta + 1) * delta :=
      mul_lt_mul_of_pos_right h2 hdelta
    have h4 : (t / delta + 1) * delta = t + delta := by field_simp
    linarith
