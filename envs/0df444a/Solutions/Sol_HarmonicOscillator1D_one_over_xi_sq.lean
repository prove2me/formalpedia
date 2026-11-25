-- Prove2me | solution 1 for HarmonicOscillator1D.one_over_xi_sq
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:47.433949+00:00
-- url     : https://prove2.me/submissions/e7fd8872-237f-424b-b94d-bd8e02c4697a

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) : (1 / Q.ξ) ^ 2 = Q.m * Q.ω / Q.ℏ := by
  unfold HarmonicOscillator.ξ
  rw [one_div, ← Real.sqrt_inv, inv_div]
  exact Real.sq_sqrt (div_pos (mul_pos Q.hm Q.hω) Q.hℏ).le
