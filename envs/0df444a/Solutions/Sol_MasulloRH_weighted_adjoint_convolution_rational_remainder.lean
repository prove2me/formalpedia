-- Prove2me | solution 1 for MasulloRH.weighted_adjoint_convolution_rational_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T08:07:58.085167+00:00
-- url     : https://prove2.me/submissions/ffdb7f87-6a1d-4de9-b1aa-3fc14d6d6997

import Mathlib
theorem solution (x b B : ℝ) (hb : |b| ≤ B) :
    let y := x+b
    let p := fun t : ℝ => 1+t^2
    let c := fun t : ℝ => t / p t
    (p y / p x)^2 =
      1 + 4*b*c y + 2*b^2/p x + (2*x*b+b^2)^2/(p x)^2
        - 4*b^2 * ((1/(p x))*(1/(p y)) - c x*c y) ∧
    |(p y / p x)^2 - 1 - 4*b*c x| ≤ (10*B^2+2*B^4)/(p x) := by
  dsimp only
  have hx : 0 < 1+x^2 := by positivity
  have hy : 0 < 1+(x+b)^2 := by positivity
  have hB : 0 ≤ B := (abs_nonneg _).trans hb
  have hb2 : b^2 ≤ B^2 := by nlinarith [sq_abs b,mul_nonneg (sub_nonneg.mpr hb) (by positivity : 0 ≤ B+|b|)]
  have hb4 : b^4 ≤ B^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hb2) (by positivity : 0 ≤ B^2+b^2)]
  constructor
  · field_simp
    <;> ring
  · have heq : ((1+(x+b)^2)/(1+x^2))^2-1-4*b*(x/(1+x^2)) =
          (2*b^2*(1+x^2)+(2*x*b+b^2)^2)/(1+x^2)^2 := by
        field_simp; ring
    rw [heq, abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity) hx).mpr
    have hquad : (2*x*b+b^2)^2 ≤ 8*x^2*b^2+2*b^4 := by nlinarith [sq_nonneg (2*x*b-b^2)]
    have upper : 2*b^2*(1+x^2)+(2*x*b+b^2)^2 ≤ (10*B^2+2*B^4)*(1+x^2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb2) (sq_nonneg x), mul_nonneg (sq_nonneg x) (by positivity : 0 ≤ B^4),sq_nonneg B]
    calc
      _ ≤ ((10*B^2+2*B^4)*(1+x^2))*(1+x^2) := mul_le_mul_of_nonneg_right upper hx.le
      _ = _ := by ring
