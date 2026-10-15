-- Prove2me | solution 1 for Multihoming.Thresholds.ePi_sub_eP
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:49:33.542979+00:00
-- url     : https://prove2.me/submissions/a9921a97-c855-427c-af57-7cc10790fecd

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
open Multihoming.Thresholds

theorem solution(t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    ePi t μ - eP t μ =
      2 * (2 * t - μ) * (t * Real.sqrt (t ^ 2 - μ ^ 2) - (t - μ) ^ 2) /
        (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by
  have hD : 0 < 4 * t ^ 2 - 3 * t * μ + μ ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * t - μ) (by linarith : (0:ℝ) < 2 * t - μ), mul_nonneg ht.le hμ]
  have hD' : 4 * t ^ 2 - 3 * t * μ + μ ^ 2 ≠ 0 := hD.ne'
  unfold ePi eP
  rw [eq_div_iff hD', sub_mul, div_mul_cancel₀ _ hD']
  ring
