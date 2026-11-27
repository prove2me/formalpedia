-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_half_square_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:59:44.365805+00:00
-- url     : https://prove2.me/submissions/8331cfeb-d6c5-433a-b2dd-8732892ba2fe

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
/-- Algebraic bound for the crossing-cell energy difference. -/
theorem solution
    (x y z R δ : ℝ) (hδ : 0 ≤ δ)
    (hx : |x| ≤ R) (hy : |y| ≤ R) (hz : |z| ≤ R)
    (hd : |x-z| ≤ δ) :
    |(x-y)^2/2-(z-y)^2/2| ≤ 2*R*δ := by
  rw [show (x-y)^2/2-(z-y)^2/2 = (x-z)*(x+z-2*y)/2 by ring,
    abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hsum : |x+z-2*y| ≤ 4*R := by
    apply abs_le.mpr
    constructor <;> linarith [abs_le.mp hx, abs_le.mp hy, abs_le.mp hz]
  have hm := mul_le_mul hd hsum (abs_nonneg _) hδ
  linarith only [hm]