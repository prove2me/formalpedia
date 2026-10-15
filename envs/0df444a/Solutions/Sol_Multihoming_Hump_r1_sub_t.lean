-- Prove2me | solution 1 for Multihoming.Hump.r1_sub_t
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:42:28.4213+00:00
-- url     : https://prove2.me/submissions/2ab9000b-9d5d-4fa8-9d52-8d7a3a850aef

import Mathlib
import Definitions.Def_Multihoming_Hump_Model
open Multihoming.Hump

theorem solution(t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    r1 t e - t = -t * ((e + 4 * t - Real.sqrt (3 * (4 * t ^ 2 - e ^ 2))) / (2 * (e + t))) ∧
    0 < e + 4 * t - Real.sqrt (3 * (4 * t ^ 2 - e ^ 2)) := by
  have hne : e + t ≠ 0 := (by linarith : (0:ℝ) < e + t).ne'
  constructor
  · unfold r1
    field_simp
    ring
  · rw [sub_pos, Real.sqrt_lt' (by linarith)]
    nlinarith [sq_nonneg (e + t)]
