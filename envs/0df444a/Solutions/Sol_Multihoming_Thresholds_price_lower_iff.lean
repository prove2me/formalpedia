-- Prove2me | solution 1 for Multihoming.Thresholds.price_lower_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:40:57.175976+00:00
-- url     : https://prove2.me/submissions/0c0d7f09-c639-4ed2-bd2f-99465d24d0d7

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
open Multihoming.Thresholds

theorem solution(t μ e : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    eP t μ < e ↔ pM t μ e < pM t 0 e := by
  unfold eP pM
  simp only [sub_zero, zero_add]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have htm := mul_pos ht hμ
  constructor
  · intro h
    nlinarith [mul_pos htm (sub_pos.mpr h)]
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg htm.le (sub_nonneg.mpr hc)]
