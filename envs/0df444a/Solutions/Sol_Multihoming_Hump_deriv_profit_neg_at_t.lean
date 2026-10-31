-- Prove2me | solution 1 for Multihoming.Hump.deriv_profit_neg_at_t
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:10:24.271986+00:00
-- url     : https://prove2.me/submissions/742b2689-98a4-4702-82f5-87a117192674

import Mathlib
import Definitions.Def_Multihoming_Hump_Model
open Multihoming.Hump

theorem solution(t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    ∃ d : ℝ, HasDerivAt (fun μ => piM t μ e) d t ∧ d < 0 := by
  have h1 : HasDerivAt (fun μ : ℝ => t - μ) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub t
  have h2 : HasDerivAt (fun μ : ℝ => e + μ) 1 t := by
    simpa using (hasDerivAt_id t).const_add e
  have h3 : HasDerivAt (fun μ : ℝ => t + μ) 1 t := by
    simpa using (hasDerivAt_id t).const_add t
  have h4 : HasDerivAt (fun μ : ℝ => 2 * t - μ) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub (2 * t)
  have hne : (t + t) * (2 * t - t) ^ 2 ≠ 0 := by
    exact mul_ne_zero (by linarith) (pow_ne_zero _ (by linarith))
  have hf := ((h1.const_mul t).mul (h2.pow 2)).div (h3.mul (h4.pow 2)) hne
  have hf' : HasDerivAt (fun μ => piM t μ e) _ t := hf
  refine ⟨-((e + t) ^ 2 / (2 * t ^ 2)), hf'.congr_deriv ?_, ?_⟩
  · norm_num
    field_simp
    ring
  · have : 0 < (e + t) ^ 2 / (2 * t ^ 2) := div_pos (by nlinarith) (by positivity)
    linarith
