-- Prove2me | solution 1 for HarmonicOscillator1D.xi_pos
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:52:47.951848+00:00
-- url     : https://prove2.me/submissions/9e4ba7f4-7f4a-4141-bf76-0d17af10c331

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) : 0 < Q.ξ := by
  unfold HarmonicOscillator.ξ
  exact Real.sqrt_pos.mpr (div_pos Q.hℏ (mul_pos Q.hm Q.hω))
