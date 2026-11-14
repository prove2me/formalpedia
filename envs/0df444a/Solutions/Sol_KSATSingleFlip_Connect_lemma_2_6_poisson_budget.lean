-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6_poisson_budget
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:47:52.377695+00:00
-- url     : https://prove2.me/submissions/9a7fd3e3-b77a-4501-8c51-12be1ec94752

import Mathlib
set_option autoImplicit false

theorem solution (ν a L n j : ℝ) (hν : 0 ≤ ν) (ha : 0 < a) (ha1 : a ≤ 1)
    (hL : 1 ≤ L) (hn : 0 < n) (hj : 0 ≤ j)
    (hclose : |j-ν*n| ≤ a*n/(4*L))
    (hsqrt : Real.sqrt (ν*n) ≤ a*n/(4*L)) :
    L*(|j-ν*n|+Real.sqrt (ν*n)) ≤ a*n/2 ∧
    j ≤ (ν+1)*n ∧
    (a*n/(4*L))^2 / (8*(ν*n + a*n/(4*L))) ≥ a^2*n/(128*(ν+1)*L^2) := by
  have hLp : 0 < L := by linarith
  have hνp : 0 < ν+1 := by linarith
  have han : 0 < a*n := mul_pos ha hn
  have hdiv : 0 ≤ a*n/(4*L) := by positivity
  have hbound : a*n/(4*L) ≤ n := by
    apply (div_le_iff₀ (by positivity : 0 < 4*L)).2
    nlinarith [mul_nonneg (show 0 ≤ 4*L-a by linarith) (le_of_lt hn)]
  have hmean : L*(|j-ν*n|+Real.sqrt (ν*n)) ≤ a*n/2 := by
    have hsum : |j-ν*n|+Real.sqrt (ν*n) ≤ 2*(a*n/(4*L)) := by linarith
    calc
      _ ≤ L*(2*(a*n/(4*L))) := mul_le_mul_of_nonneg_left hsum (le_of_lt hLp)
      _ = a*n/2 := by field_simp; ring
  refine ⟨hmean, ?_, ?_⟩
  · have := (le_abs_self (j-ν*n)).trans hclose
    nlinarith
  · have hden : 0 < 8*(ν*n + a*n/(4*L)) := by positivity
    have hden' : 0 < 128*(ν+1)*L^2 := by positivity
    apply (div_le_div_iff₀ hden' hden).2
    have hn1 : 0 ≤ (ν+1)*n - (ν*n + a*n/(4*L)) := by nlinarith
    have hm := mul_nonneg (sq_nonneg (a*n/(4*L))) hn1
    have hn0 : n ≠ 0 := ne_of_gt hn
    have hL0 : L ≠ 0 := ne_of_gt hLp
    field_simp at hm ⊢
    nlinarith
