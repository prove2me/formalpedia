-- Prove2me | solution 1 for LNChannels.RateBounds.eq_17_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:40:41.150263+00:00
-- url     : https://prove2.me/submissions/4f5eb9aa-e100-4f6d-a079-4b70d04a27a1

import Mathlib
set_option autoImplicit false

theorem solution (B κ C : ℝ) (hB : 0 < B) (hκ : 0 < κ) (hκC : (Real.exp C - 1) / B ≤ κ) :
    ∀ m : ℝ, 0 < m → 0 < C / (1 - Real.exp κ) + B / (Real.exp (κ * m) - 1) + m := by
  intro m hm
  have hκC' : Real.exp C - 1 ≤ κ * B := by rwa [div_le_iff₀ hB] at hκC
  have hE : 0 < Real.exp κ - 1 := by linarith [Real.add_one_lt_exp hκ.ne']
  have hu : 0 < κ * m := mul_pos hκ hm
  have hx : 0 < Real.exp (κ * m) - 1 := by linarith [Real.add_one_lt_exp hu.ne']
  have hB' : 0 < B / (Real.exp (κ * m) - 1) := div_pos hB hx
  have h1 : C / (1 - Real.exp κ) = -(C / (Real.exp κ - 1)) := by
    rw [show 1 - Real.exp κ = -(Real.exp κ - 1) by ring, div_neg]
  rcases le_or_gt C 0 with hC | hC
  · have : C / (Real.exp κ - 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hC hE.le
    rw [h1]; linarith
  · have key : (C - κ * m) * (Real.exp (κ * m) - 1) < Real.exp C - 1 := by
      rcases le_or_gt (C - κ * m) 0 with hw | hw
      · have h2 : (C - κ * m) * (Real.exp (κ * m) - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw hx.le
        have h3 : 0 < Real.exp C - 1 := by linarith [Real.add_one_lt_exp hC.ne']
        linarith
      · have h2 : Real.exp C = Real.exp (κ * m) * Real.exp (C - κ * m) := by
          rw [← Real.exp_add]; ring_nf
        have h3 := Real.add_one_le_exp (C - κ * m)
        have h4 : 0 < Real.exp (κ * m) := Real.exp_pos _
        nlinarith [mul_le_mul_of_nonneg_left h3 h4.le, Real.add_one_lt_exp hu.ne']
    have hCE : C / (Real.exp κ - 1) ≤ C / κ :=
      div_le_div_of_nonneg_left hC.le hκ (by linarith [Real.add_one_le_exp κ])
    have h5 : C - κ * m < κ * B / (Real.exp (κ * m) - 1) := by
      rw [lt_div_iff₀ hx]; linarith
    have h6 : C / κ < B / (Real.exp (κ * m) - 1) + m := by
      rw [div_lt_iff₀ hκ]
      have : (B / (Real.exp (κ * m) - 1) + m) * κ = κ * B / (Real.exp (κ * m) - 1) + κ * m := by ring
      linarith
    rw [h1]; linarith
