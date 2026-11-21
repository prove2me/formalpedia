-- Prove2me | solution 1 for MasulloRH.rational_strip_weight_translation_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:27:18.785144+00:00
-- url     : https://prove2.me/submissions/a50fb2ba-463b-4f95-9577-7f5bcafc78f9

import Definitions.Def_MasulloRH_WeightedStripJetSpace

open MasulloRH

theorem solution (b p : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p) (x t : ℝ) :
    rationalStripWeight b p x / rationalStripWeight b p (x+t) ≤
      (2*(1+t^2)) ^ (p/2) * Real.exp (b*|t|) := by
  let X := 1 + x^2
  let Y := 1 + (x+t)^2
  let D := 2*(1+t^2)
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hpoly : Y ≤ D*X := by
    dsimp [X,Y,D]
    nlinarith [sq_nonneg (x-t), sq_nonneg (x*t)]
  have hr : Y^(p/2) ≤ D^(p/2) * X^(p/2) := by
    rw [← Real.mul_rpow hD.le hX.le]
    exact Real.rpow_le_rpow hY.le hpoly (by positivity)
  have he : Real.exp (b*|x+t|-b*|x|) ≤ Real.exp (b*|t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (abs_add_le x t) hb]
  have hfac : rationalStripWeight b p x / rationalStripWeight b p (x+t) =
      (Y^(p/2) / X^(p/2)) * Real.exp (b*|x+t|-b*|x|) := by
    change (X^(-p/2)*Real.exp (-b*|x|)) / (Y^(-p/2)*Real.exp (-b*|x+t|)) = _
    rw [neg_div, Real.rpow_neg hX.le, Real.rpow_neg hY.le, Real.exp_sub]
    simp only [neg_mul, Real.exp_neg]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hX (p/2)), ne_of_gt (Real.rpow_pos_of_pos hY (p/2))]
    <;> ring
  rw [hfac]
  exact mul_le_mul ((div_le_iff₀ (Real.rpow_pos_of_pos hX _)).2 hr) he
    (Real.exp_pos _).le (Real.rpow_pos_of_pos hD _).le
