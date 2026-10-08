-- Prove2me | solution 1 for MazurHuang.N19.minimal_affine_x_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:40:32.49443+00:00
-- url     : https://prove2.me/submissions/afdd5542-0383-4434-90de-ceb64be14c2a

/-
Rational points on the order-nineteen diamond quotient
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_MazurHuang_N19_short_flex_factor_is_rational_cube
import Theorems.Thm_MazurHuang_N19_good_affine_x_eq_zero

/-- Cube descent gives a dual preimage; good-model classification fixes its x-coordinate. -/
private theorem short_x_zero {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 + (2*x+4)^2) : x = 0 := by
  obtain ⟨r, hr⟩ := MazurHuang.N19.short_flex_factor_is_rational_cube hcurve
  by_cases hr0 : r = 0
  · rw [hr0] at hr
    norm_num at hr
    have hy : y = 2*x+4 := by linarith
    rw [hy] at hcurve
    have hx3 : x ^ 3 = 0 := by linarith
    exact eq_zero_of_pow_eq_zero hx3
  have hy : y = r ^ 3 + 2*x+4 := by linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 4*x+8) := by
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3*x-3*r^2-4*r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r^2+4*r/3 := by dsimp [d] at hd; linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r^3 = 0 := by linarith
    exact eq_zero_of_pow_eq_zero this
  let s : ℚ := 456*r/d
  let t : ℚ := 9*s*r+6*s+684
  have hdual : t^2 = s^3-3*(6*s+228)^2 := by
    dsimp only [t,s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 16842816*hrel
  have hxmap : (s^3-144*s^2-16416*s-623808)/(81*s^2) = x := by
    dsimp only [s]
    field_simp [hd,hr0]
    dsimp only [d]
    linear_combination -16842816*hrel
  have hgood : (t/27)^2 = ((s-228)/9)^3+(8*((s-228)/9)+76)^2 := by
    linear_combination hdual/729
  have hg := MazurHuang.N19.good_affine_x_eq_zero hgood
  have hs : s = 228 := by linarith
  rw [hs] at hxmap
  norm_num at hxmap
  exact hxmap.symm
theorem solution {u v : ℚ} (h : v ^ 2 + v = u ^ 3 + u ^ 2 + u) : u = 0 := by
  have hs : (8*v+4)^2 = (4*u)^3+(2*(4*u)+4)^2 := by linear_combination 64*h
  have hx := short_x_zero hs
  linarith
