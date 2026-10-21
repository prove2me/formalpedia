-- Prove2me | solution 1 for MultiPriceOnline.Ratios.x_div_one_sub_exp_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:36:02.917302+00:00
-- url     : https://prove2.me/submissions/64be4e39-28f3-4b87-991e-89d8df90eba2

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

set_option autoImplicit false

theorem solution :
    StrictMonoOn (fun x : ℝ => if x = 0 then 1 else x / (1 - Real.exp (-x))) (Set.Icc 0 1) := by
  have hpos : ∀ t : ℝ, 0 < t → 0 < 1 - Real.exp (-t) := by
    intro t ht
    have : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · subst h0
    have hy0 : 0 < y := hxy
    have hy' : y ≠ 0 := hy0.ne'
    simp only [if_true, hy', if_false]
    have := hpos y hy0
    have h2 : 1 - y < Real.exp (-y) := by
      have := Real.add_one_lt_exp (x := -y) (by linarith)
      linarith
    rw [lt_div_iff₀ this]
    linarith
  · have hx' : x ≠ 0 := h0.ne'
    have hy0 : 0 < y := lt_trans h0 hxy
    have hy' : y ≠ 0 := hy0.ne'
    simp only [hx', hy', if_false]
    have hhx := hpos x h0
    have hhy := hpos y hy0
    rw [div_lt_div_iff₀ hhx hhy]
    have key := strictConvexOn_exp.2 (Set.mem_univ (-y)) (Set.mem_univ 0)
      (show (-y) ≠ 0 by intro h; apply hy'; linarith)
      (show 0 < x / y by positivity)
      (show 0 < 1 - x / y by rw [sub_pos, div_lt_one hy0]; exact hxy)
      (show x / y + (1 - x / y) = 1 by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at key
    have e : x / y * -y = -x := by field_simp
    rw [e] at key
    have k2 : x / y * Real.exp (-y) + (1 - x / y) - Real.exp (-x) > 0 := by linarith
    have k3 : x * (1 - Real.exp (-y)) < y * (1 - Real.exp (-x)) := by
      have : y * (x / y * Real.exp (-y) + (1 - x / y) - Real.exp (-x)) > 0 := mul_pos hy0 k2
      have e2 : y * (x / y * Real.exp (-y) + (1 - x / y) - Real.exp (-x))
          = x * Real.exp (-y) + y - x - y * Real.exp (-x) := by field_simp; ring
      nlinarith
    exact k3
