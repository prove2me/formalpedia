-- Prove2me | solution 1 for NadlerCLS.eq_C_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:07:12.35888+00:00
-- url     : https://prove2.me/submissions/0ec796e1-0389-43d6-bd1b-f5fbc4fcb98b

import Mathlib
import Definitions.Def_NadlerCLS_dp

set_option autoImplicit false

open NadlerCLS in
theorem solution {α : Type*} (p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (f : α → α) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (x y : α) (hxy : x ≠ y) (hfxy : f x ≠ f y)
    (hx : p (f x) < p x - δ) (hy : p (f y) < p y - δ) :
    dp p (f x) (f y) < dp p x y - δ ∧ dp p x y - δ ≤ (1 - δ / 2) * dp p x y := by
  classical
  have e1 : dp p (f x) (f y) = 1 + max (p (f x)) (p (f y)) := by unfold dp; simp [hfxy]
  have e2 : dp p x y = 1 + max (p x) (p y) := by unfold dp; simp [hxy]
  rw [e1, e2]
  have hmax : max (p x) (p y) ≤ 1 := max_le (hp x).2 (hp y).2
  constructor
  · have : max (p (f x)) (p (f y)) < max (p x) (p y) - δ := by
      rcases le_total (p (f x)) (p (f y)) with h | h
      · rw [max_eq_right h]; linarith [le_max_right (p x) (p y)]
      · rw [max_eq_left h]; linarith [le_max_left (p x) (p y)]
    linarith
  · nlinarith
