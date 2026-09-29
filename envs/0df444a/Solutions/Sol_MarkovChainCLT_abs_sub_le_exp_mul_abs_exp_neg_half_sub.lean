-- Prove2me | solution 1 for MarkovChainCLT.abs_sub_le_exp_mul_abs_exp_neg_half_sub
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:23:57.522549+00:00
-- url     : https://prove2.me/submissions/f84a587a-c12e-4d4a-87ad-d6fbc99e76a1

import Mathlib.Analysis.SpecialFunctions.Exp

open Filter
open scoped Topology

set_option maxHeartbeats 2000000

theorem solution (B a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haB : a ≤ B) (hbB : b ≤ B) :
    |a - b| ≤ 2 * Real.exp (B / 2) * |Real.exp (-a / 2) - Real.exp (-b / 2)| := by
  have key : ∀ p q : ℝ, 0 ≤ p → p ≤ q → q ≤ B →
      q - p ≤ 2 * Real.exp (B / 2) * (Real.exp (-p / 2) - Real.exp (-q / 2)) := by
    intro p q hp hpq hqB
    have hfac : Real.exp (-p / 2) - Real.exp (-q / 2)
        = Real.exp (-q / 2) * (Real.exp ((q - p) / 2) - 1) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    have h1 : Real.exp (-B / 2) ≤ Real.exp (-q / 2) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h2 : (q - p) / 2 ≤ Real.exp ((q - p) / 2) - 1 := by
      have := Real.add_one_le_exp ((q - p) / 2)
      linarith
    have h3 : (0 : ℝ) ≤ (q - p) / 2 := by linarith
    have h4 : Real.exp (-B / 2) * ((q - p) / 2)
        ≤ Real.exp (-q / 2) * (Real.exp ((q - p) / 2) - 1) :=
      mul_le_mul h1 h2 h3 (Real.exp_pos _).le
    rw [hfac]
    have h5 : Real.exp (B / 2) * Real.exp (-B / 2) = 1 := by
      rw [← Real.exp_add, show B / 2 + -B / 2 = 0 by ring, Real.exp_zero]
    nlinarith [Real.exp_pos (B / 2), h4, h5]
  rcases le_total a b with hab | hab
  · have h := key a b ha hab hbB
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by nlinarith [h, Real.exp_pos (B/2)])]
    linarith
  · have h := key b a hb hab haB
    rw [abs_of_nonneg (by linarith)]
    rw [abs_sub_comm, abs_of_nonneg (by nlinarith [h, Real.exp_pos (B/2)])]
    linarith
