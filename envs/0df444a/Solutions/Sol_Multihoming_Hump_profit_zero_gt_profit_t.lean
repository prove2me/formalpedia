-- Prove2me | solution 1 for Multihoming.Hump.profit_zero_gt_profit_t
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:39:10.982729+00:00
-- url     : https://prove2.me/submissions/34b01921-608b-408a-bd29-ee0b00a3eef4

import Mathlib
import Definitions.Def_Multihoming_Hump_Model
open Multihoming.Hump

theorem solution(t e : ℝ) (ht : 0 < t) (he0 : 0 < e) :
    piM t t e < piM t 0 e := by
  unfold piM
  rw [sub_self, mul_zero, zero_mul, zero_div]
  simp only [sub_zero, add_zero]
  positivity
