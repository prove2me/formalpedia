-- Prove2me | solution 1 for Multihoming.Thresholds.eP_lt_ePi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:49:35.771444+00:00
-- url     : https://prove2.me/submissions/a5e8eb77-6914-4662-a313-503e6a80e9d8

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
open Multihoming.Thresholds

theorem solution(t μ : ℝ) (ht : 0 < t) (hμ : 0 < μ) (hμt : μ < t) :
    (t * Real.sqrt (t ^ 2 - μ ^ 2) > (t - μ) ^ 2 ↔
      μ * (t - μ) * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) > 0) ∧
    eP t μ < ePi t μ := by
  have ha : 0 < t - μ := by linarith
  have hD : 0 < 4 * t ^ 2 - 3 * t * μ + μ ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * t - μ) (by linarith : (0:ℝ) < 2 * t - μ), mul_pos ht hμ]
  have hL : t * Real.sqrt (t ^ 2 - μ ^ 2) > (t - μ) ^ 2 := by
    have h3 : (t - μ) ^ 3 < (t + μ) * t ^ 2 := by
      have := pow_lt_pow_left₀ (by linarith : t - μ < t) ha.le (by norm_num : (3:ℕ) ≠ 0)
      nlinarith [mul_pos (pow_pos ht 2) hμ]
    have h4 : (t - μ) * (t - μ) ^ 3 < (t - μ) * ((t + μ) * t ^ 2) := mul_lt_mul_of_pos_left h3 ha
    have hs : (t - μ) ^ 2 / t < Real.sqrt (t ^ 2 - μ ^ 2) := by
      rw [Real.lt_sqrt (by positivity), div_pow, div_lt_iff₀ (by positivity)]
      nlinarith [h4]
    rw [div_lt_iff₀ ht] at hs
    linarith
  have hR : μ * (t - μ) * (4 * t ^ 2 - 3 * t * μ + μ ^ 2) > 0 := mul_pos (mul_pos hμ ha) hD
  refine ⟨⟨fun _ => hR, fun _ => hL⟩, ?_⟩
  have hsub : ePi t μ - eP t μ = 2 * (2 * t - μ) * (t * Real.sqrt (t ^ 2 - μ ^ 2) - (t - μ) ^ 2) / (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by
    have hD' : 4 * t ^ 2 - 3 * t * μ + μ ^ 2 ≠ 0 := hD.ne'
    unfold ePi eP
    rw [eq_div_iff hD', sub_mul, div_mul_cancel₀ _ hD']
    ring
  have hp : 0 < 2 * (2 * t - μ) * (t * Real.sqrt (t ^ 2 - μ ^ 2) - (t - μ) ^ 2) / (4 * t ^ 2 - 3 * t * μ + μ ^ 2) := by
    apply div_pos _ hD
    apply mul_pos (by linarith)
    linarith
  linarith
