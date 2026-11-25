-- Prove2me | solution 1 for HarmonicOscillator1D.one_over_xi
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T18:54:45.476658+00:00
-- url     : https://prove2.me/submissions/2074086d-1f0e-4ced-9fbe-4ea76b54ed68

import Mathlib
import Definitions.Def_HO1D_basic

open HarmonicOscillator1D HarmonicOscillator1D.HarmonicOscillator

theorem solution (Q : HarmonicOscillator) : 1 / Q.ξ = Real.sqrt (Q.m * Q.ω / Q.ℏ) := by
  unfold HarmonicOscillator.ξ
  rw [one_div, ← Real.sqrt_inv, inv_div]
