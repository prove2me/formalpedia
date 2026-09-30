-- Prove2me | solution 1 for NicaiseDelayWave.InternalInstab.delay_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:08:33.21514+00:00
-- url     : https://prove2.me/submissions/774b6f73-6694-4d7a-aa4d-22605be7da85

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false

theorem solution (μ₁ μ₂ α τ Λ : ℝ) (l : ℕ) (hμ₁ : 0 < μ₁) (hμ : μ₁ < μ₂)
    (hα₀ : 0 < α) (hα₁ : α < (μ₂ - μ₁) / 2) (hΛ : 0 < Λ) (hτ : 0 < τ)
    (h : α ^ 2 + (2 * l + 1) ^ 2 * Real.pi ^ 2 / τ ^ 2 = Λ ^ 2) :
    (2 * l + 1) * Real.pi / Λ < τ ∧
      ((μ₂ - μ₁) ^ 2 / 4 < Λ ^ 2 →
        τ < (2 * l + 1) * Real.pi / Real.sqrt (Λ ^ 2 - (μ₂ - μ₁) ^ 2 / 4)) := by
  let s : ℝ := (2 * l + 1) * Real.pi
  let r : ℝ := s / τ
  have hs : 0 < s := by dsimp [s]; positivity
  have hr : 0 < r := div_pos hs hτ
  have he : α ^ 2 + r ^ 2 = Λ ^ 2 := by
    simpa only [r, s, div_pow, mul_pow] using h
  constructor
  · have hrl : r < Λ := by nlinarith [sq_pos_of_pos hα₀]
    have hmul : s < Λ * τ := (div_lt_iff₀ hτ).mp hrl
    exact (div_lt_iff₀ hΛ).mpr (by simpa only [s, mul_comm] using hmul)
  · intro hb
    have hd : 0 < μ₂ - μ₁ := sub_pos.mpr hμ
    have hasq : α ^ 2 < (μ₂ - μ₁) ^ 2 / 4 := by
      nlinarith [mul_pos (sub_pos.mpr hα₁) (show 0 < (μ₂ - μ₁) / 2 + α by linarith)]
    have hp : 0 < Λ ^ 2 - (μ₂ - μ₁) ^ 2 / 4 := sub_pos.mpr hb
    have hroot : 0 < Real.sqrt (Λ ^ 2 - (μ₂ - μ₁) ^ 2 / 4) := Real.sqrt_pos.mpr hp
    have hsquare := Real.sq_sqrt hp.le
    have hrootr : Real.sqrt (Λ ^ 2 - (μ₂ - μ₁) ^ 2 / 4) < r := by
      nlinarith
    have hmul : Real.sqrt (Λ ^ 2 - (μ₂ - μ₁) ^ 2 / 4) * τ < s :=
      (lt_div_iff₀ hτ).mp hrootr
    exact (lt_div_iff₀ hroot).mpr (by simpa only [s, mul_comm] using hmul)
