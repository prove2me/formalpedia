-- Prove2me | solution 2 for HarmonicOscillator1D.xi_sq
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:42.883354+00:00
-- url     : https://prove2.me/submissions/67da94c0-ebdc-43a9-9576-b5d8364b9126

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) : Q.ξ ^ 2 = Q.ℏ / (Q.m * Q.ω) := by
  unfold HarmonicOscillator.ξ
  exact Real.sq_sqrt (div_pos Q.hℏ (mul_pos Q.hm Q.hω)).le
