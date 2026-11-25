-- Prove2me | solution 1 for HarmonicOscillator1D.xi_sq
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:40.374453+00:00
-- url     : https://prove2.me/submissions/f189b348-5dcd-4be9-a93d-0785f67dca32

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) : Q.ξ ^ 2 = Q.ℏ / (Q.m * Q.ω) := by
  unfold HarmonicOscillator.ξ
  exact Real.sq_sqrt (div_pos Q.hℏ (mul_pos Q.hm Q.hω)).le
