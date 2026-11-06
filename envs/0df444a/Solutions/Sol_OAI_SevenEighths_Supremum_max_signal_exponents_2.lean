-- Prove2me | solution 2 for OAI.SevenEighths.Supremum.max_signal_exponents
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:41.920598+00:00
-- url     : https://prove2.me/submissions/a0390870-d56a-4178-8e57-b116cfc29462

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Supremum
noncomputable section
theorem solution (β ω σ c : ℝ) :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by
  unfold continuationMargin
  by_cases h : β - 7 / 8 - ω ≤ σ
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · push_neg at h
    rw [min_eq_right h.le, max_eq_right (by linarith)]
