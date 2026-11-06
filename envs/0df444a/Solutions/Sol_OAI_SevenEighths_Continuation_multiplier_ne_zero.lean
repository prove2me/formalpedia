-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.multiplier_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:48.703226+00:00
-- url     : https://prove2.me/submissions/d5aad96c-aab8-42ee-b9b9-f0ea686694e1

import Mathlib.Analysis.Complex.HalfPlane

set_option autoImplicit false

theorem solution {H : ℂ → ℂ} {s : ℂ}
    (h : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : H s ≠ 0 := by
  intro hs
  norm_num [hs] at h
