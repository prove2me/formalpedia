-- Prove2me | solution 1 for Multihoming.Hump.deriv_profit_pos_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:10:22.20699+00:00
-- url     : https://prove2.me/submissions/dbbe238b-4bde-41dc-81f2-e02e23c48f03

import Mathlib
import Definitions.Def_Multihoming_Hump_Model
open Multihoming.Hump

theorem solution(t e : ℝ) (ht : 0 < t) (he0 : 0 < e) (he : e < 2 * t) :
    ∃ d : ℝ, HasDerivAt (fun μ => piM t μ e) d 0 ∧ 0 < d := by
  have h1 : HasDerivAt (fun μ : ℝ => t - μ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub t
  have h2 : HasDerivAt (fun μ : ℝ => e + μ) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add e
  have h3 : HasDerivAt (fun μ : ℝ => t + μ) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add t
  have h4 : HasDerivAt (fun μ : ℝ => 2 * t - μ) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub (2 * t)
  have hne : (t + 0) * (2 * t - 0) ^ 2 ≠ 0 := by
    rw [add_zero, sub_zero]; exact mul_ne_zero ht.ne' (pow_ne_zero _ (by linarith))
  have hf := ((h1.const_mul t).mul (h2.pow 2)).div (h3.mul (h4.pow 2)) hne
  have hf' : HasDerivAt (fun μ => piM t μ e) _ 0 := hf
  refine ⟨e * (2 * t - e) / (4 * t ^ 2), hf'.congr_deriv ?_, ?_⟩
  · norm_num
    field_simp
    ring
  · apply div_pos (mul_pos he0 (by linarith)) (by positivity)
