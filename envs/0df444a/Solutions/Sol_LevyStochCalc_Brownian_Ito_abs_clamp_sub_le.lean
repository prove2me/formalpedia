-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.abs_clamp_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T06:58:09.930178+00:00
-- url     : https://prove2.me/submissions/fc37d3a0-9d26-4683-a00c-38c2ca02f30f

import Mathlib

theorem solution {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by
  have hy1 : -C ≤ y := (abs_le.mp hy).1
  have hy2 : y ≤ C := (abs_le.mp hy).2
  rcases le_total x (-C) with hx | hx
  · rw [min_eq_right (le_trans hx (by linarith)), max_eq_left hx]
    rw [abs_of_nonpos (by linarith : -C - y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  rcases le_total x C with hx2 | hx2
  · rw [min_eq_right hx2, max_eq_right hx]
  · rw [min_eq_left hx2, max_eq_right (by linarith : -C ≤ C)]
    rw [abs_of_nonneg (by linarith : 0 ≤ C - y), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
