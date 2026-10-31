-- Prove2me | solution 1 for ICOTheory.Signaling.eq_25_alphaStar_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:54:46.060788+00:00
-- url     : https://prove2.me/submissions/9b745b8d-e4b9-434e-a69c-2799f488e1e2

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar
open ICOTheory.Signaling

theorem solution{μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ) :
    0 < alphaStar μH μL σ γ ∧ alphaStar μH μL σ γ < 1 := by
  unfold alphaStar
  have ha0 : 0 < 4 * μH - 4 * μL := by linarith
  have hs : 0 < σ ^ 2 * γ := by positivity
  have hsq : Real.sqrt ((4 * μH - 4 * μL) * (4 * μH - 4 * μL + 2 * σ ^ 2 * γ)) < 4 * μH - 4 * μL + σ ^ 2 * γ := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith [mul_pos hs hs]
  have hsq2 : 4 * μH - 4 * μL < Real.sqrt ((4 * μH - 4 * μL) * (4 * μH - 4 * μL + 2 * σ ^ 2 * γ)) := by
    rw [Real.lt_sqrt (by linarith)]; nlinarith [mul_pos ha0 hs]
  constructor
  · apply div_pos (by linarith) hs
  · rw [div_lt_one hs]; linarith
