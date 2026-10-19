-- Prove2me | solution 1 for ModernOnlineLearning.Adaptive.lemma_4_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:00:01.534445+00:00
-- url     : https://prove2.me/submissions/22c2a6f7-0bf5-436d-b2f6-102802fe3471

import Mathlib
set_option autoImplicit false

theorem solution (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hx : 0 ≤ x)
    (h : x - Real.sqrt (a * x + b) ≤ c) :
    x ≤ a / 2 + c + Real.sqrt (a ^ 2 / 4 + b + a * c) ∧
      a / 2 + c + Real.sqrt (a ^ 2 / 4 + b + a * c) ≤
        a + c + Real.sqrt (b + a * c) := by
  have hr0 : 0 ≤ Real.sqrt (a ^ 2 / 4 + b + a * c) := Real.sqrt_nonneg _
  have hs0 : 0 ≤ Real.sqrt (b + a * c) := Real.sqrt_nonneg _
  constructor
  · by_cases hxc : x - c ≤ 0
    · linarith
    · push_neg at hxc
      have h1 : x - c ≤ Real.sqrt (a * x + b) := by linarith
      have h2 : (x - c) ^ 2 ≤ a * x + b := (Real.le_sqrt' hxc).mp h1
      have hrr : Real.sqrt (a ^ 2 / 4 + b + a * c) ^ 2 = a ^ 2 / 4 + b + a * c :=
        Real.sq_sqrt (by positivity)
      by_contra hcon
      push_neg at hcon
      nlinarith
  · have hs : Real.sqrt (a ^ 2 / 4 + b + a * c) ≤ a / 2 + Real.sqrt (b + a * c) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have := Real.sq_sqrt (show 0 ≤ b + a * c by positivity)
      nlinarith [mul_nonneg ha hs0]
    linarith
