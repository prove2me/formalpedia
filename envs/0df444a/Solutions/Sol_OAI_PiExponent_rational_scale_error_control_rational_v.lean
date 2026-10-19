-- Prove2me | solution 1 for OAI.PiExponent.rational_scale_error_control_rational_v
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:47:12.987477+00:00
-- url     : https://prove2.me/submissions/086873b4-6b07-4304-85a2-502b94c9dc2d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order

theorem solution
    (b s g c : ℝ) (hb : 0 ≤ b) (hs : 0 < s) (hg : 0 < g)
    (hcapacity : 4 * (b + 2 * s) * (1 + g) / g < c) :
    ∃ v : ℚ, 0 < v ∧ (b + 2 * s) / (v : ℝ) < g / 2 ∧
      1 + g < c / (v : ℝ) := by
  have hbs : 0 < b + 2 * s := by linarith
  have hcap : 4 * (b + 2 * s) * (1 + g) < c * g := by
    rwa [div_lt_iff₀ hg] at hcapacity
  have hlt : 2 * (b + 2 * s) / g < c / (1 + g) := by
    rw [div_lt_div_iff₀ hg (by linarith)]
    nlinarith
  obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn hlt
  have hvpos : (0 : ℝ) < v := lt_trans (by positivity) hv1
  refine ⟨v, by exact_mod_cast hvpos, ?_, ?_⟩
  · rw [div_lt_iff₀ hvpos]
    rw [div_lt_iff₀ hg] at hv1
    linarith
  · rw [lt_div_iff₀ hvpos]
    rw [lt_div_iff₀ (by linarith)] at hv2
    linarith
