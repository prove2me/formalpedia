-- Prove2me | solution 1 for MasulloRH.two_prime_gram_frechet_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T17:48:46.383933+00:00
-- url     : https://prove2.me/submissions/e18617b7-cbc5-4d4d-8042-a0ba050bf5ee

import Mathlib

theorem solution :
    let a : ℝ := 2 / (3 + Real.sqrt 2)^2
    let b : ℝ := 3 / (4 + Real.sqrt 3)^2
    1 - 9*a - 9*b + 9*a*b < -(1/2 : ℝ) ∧
    ∀ (m00 m01 m10 m11 : ℝ), 0 ≤ m00 →
      m00 + m01 + m10 + m11 = 1 →
      1/2 < |(m10+m11) - 9*a| + |(m01+m11) - 9*b| + |m11 - 9*a*b| := by
  dsimp only
  let a : ℝ := 2 / (3 + Real.sqrt 2)^2
  let b : ℝ := 3 / (4 + Real.sqrt 3)^2
  change 1 - 9*a - 9*b + 9*a*b < -(1/2 : ℝ) ∧ _
  have s2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have s3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have u2 : Real.sqrt 2 < 3/2 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt 2 - 3/2 by linarith) (show 0 ≤ Real.sqrt 2 + 3/2 by positivity)]
  have u3 : Real.sqrt 3 < 2 := by
    by_contra! h
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt 3 - 2 by linarith) (show 0 ≤ Real.sqrt 3 + 2 by positivity)]
  have al : 1/10 < a := by
    dsimp [a]; apply (lt_div_iff₀ (by positivity)).2; nlinarith
  have bl : 1/12 < b := by
    dsimp [b]; apply (lt_div_iff₀ (by positivity)).2; nlinarith
  have au : a < 1 := by
    dsimp [a]; apply (div_lt_iff₀ (by positivity)).2; nlinarith [Real.sqrt_nonneg 2]
  have gap : 1 - 9*a - 9*b + 9*a*b < -(1/2 : ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr au) (sub_pos.mpr bl)]
  refine ⟨gap, ?_⟩
  intro m00 m01 m10 m11 h0 hsum
  change 1/2 < |(m10+m11) - 9*a| + |(m01+m11) - 9*b| + |m11 - 9*a*b|
  linarith [neg_abs_le ((m10+m11)-9*a), neg_abs_le ((m01+m11)-9*b),
    le_abs_self (m11-9*a*b)]
