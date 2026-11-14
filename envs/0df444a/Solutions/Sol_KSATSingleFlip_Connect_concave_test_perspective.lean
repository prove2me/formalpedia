-- Prove2me | solution 1 for KSATSingleFlip.Connect.concave_test_perspective
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:31:44.27492+00:00
-- url     : https://prove2.me/submissions/ff660b01-c9d1-4072-8597-a332a9d1983c

import Mathlib
set_option autoImplicit false
open Set

theorem solution (ψ : ℝ → ℝ) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (x0 x1 y0 y1 a b : ℝ)
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hy0 : 0 ≤ y0) (hy1 : 0 ≤ y1)
    (hxs : 0 < x0+x1) (hys : 0 < y0+y1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*(x0+x1)*ψ (x1/(x0+x1)) + b*(y0+y1)*ψ (y1/(y0+y1)) ≤
      (a*(x0+x1)+b*(y0+y1))*ψ ((a*x1+b*y1)/(a*(x0+x1)+b*(y0+y1))) := by
  let X := x0+x1
  let Y := y0+y1
  let S := a*X+b*Y
  have hX : 0 < X := hxs
  have hY : 0 < Y := hys
  have hS : 0 < S := by
    dsimp [S]
    by_cases ha0 : a = 0
    · have hbpos : 0 < b := by linarith
      have := mul_pos hbpos hY
      nlinarith
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have := mul_pos hapos hX
      have := mul_nonneg hb hY.le
      nlinarith
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hY0 : Y ≠ 0 := ne_of_gt hY
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hxmem : x1/X ∈ Icc 0 1 := by
    constructor
    · positivity
    · apply (div_le_one₀ hX).2
      dsimp [X]
      linarith
  have hymem : y1/Y ∈ Icc 0 1 := by
    constructor
    · positivity
    · apply (div_le_one₀ hY).2
      dsimp [Y]
      linarith
  let A := a*X/S
  let B := b*Y/S
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAB : A+B=1 := by
    dsimp [A,B]
    rw [← add_div]
    change S/S = 1
    exact div_self hS0
  have harg : A*(x1/X)+B*(y1/Y) = (a*x1+b*y1)/S := by
    dsimp [A,B]
    field_simp
  have hh := hψ.2 hxmem hymem hA hB hAB
  simp only [smul_eq_mul] at hh
  rw [harg] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (le_of_lt hS)
  dsimp [A,B] at hh'
  field_simp at hh'
  dsimp [X,Y,S] at *
  nlinarith [hh']
