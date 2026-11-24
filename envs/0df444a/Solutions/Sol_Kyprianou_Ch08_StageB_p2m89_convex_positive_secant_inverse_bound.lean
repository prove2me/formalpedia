-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m89_convex_positive_secant_inverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:38:34.926268+00:00
-- url     : https://prove2.me/submissions/cd0b2887-4f17-4687-b8a0-c371300740cf

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Convex.Slope
set_option autoImplicit false
open Set

/-- Compare two secants through the origin. -/
theorem solution :
    ∀ (f : ℝ → ℝ), f 0 = 0 → ConvexOn ℝ (Ici (0 : ℝ)) f →
      ∀ x y : ℝ, 0 < x → 0 < y →
      |x - y| * f y ≤ |f x - f y| * y := by
  intro f h0 hc x y hx hy
  have hcross (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
      f a * b ≤ f b * a := by
    have hs := hc.secant_mono (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      (Set.mem_Ici.mpr ha.le) (Set.mem_Ici.mpr hb.le) ha.ne' hb.ne' hab
    simp only [h0, sub_zero] at hs
    exact (div_le_div_iff₀ ha hb).mp hs
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hmul := mul_le_mul_of_nonneg_right (le_abs_self (f x - f y)) hy.le
    nlinarith only [hcross y x hy hx h, hmul]
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hmul := mul_le_mul_of_nonneg_right (neg_le_abs (f x - f y)) hy.le
    nlinarith only [hcross x y hx hy h, hmul]
