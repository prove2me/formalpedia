-- Prove2me | solution 1 for Multihoming.Hump.r1_r2_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:41:23.280854+00:00
-- url     : https://prove2.me/submissions/05bd2eca-5ee0-4654-95e0-531fac2aaa71

import Mathlib
import Definitions.Def_Multihoming_Hump_Model
open Multihoming.Hump

theorem solution(t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    0 < r1 t e ∧ 0 < r2 t e := by
  have hgt : 2 * t - e < Real.sqrt (3 * (4 * t ^ 2 - e ^ 2)) := by
    rw [Real.lt_sqrt (by linarith)]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * t - e) (by linarith : (0:ℝ) < t + e)]
  have hden : (0:ℝ) < 2 * (e + t) := by linarith
  unfold r1 r2
  constructor
  · apply div_pos _ hden
    nlinarith [mul_lt_mul_of_pos_left hgt ht]
  · apply div_pos _ hden
    apply mul_pos ht
    linarith
