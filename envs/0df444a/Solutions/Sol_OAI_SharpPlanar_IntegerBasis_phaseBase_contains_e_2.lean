-- Prove2me | solution 2 for OAI.SharpPlanar.IntegerBasis.phaseBase_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-06T03:48:41.200704+00:00
-- url     : https://prove2.me/submissions/a86c39a6-699c-4db5-8cd1-7031b85fcf74

import Mathlib
import Definitions.Def_OAIQ098E031

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open OAI.SharpPlanar.IntegerBasis
open OAI.SharpPlanar.IntegerIntervals

theorem solution : phaseBase.Contains (phase12 1) := by
  have hphase : phase12 1 = Complex.exp (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) := by
    simp [phase12]
    congr 1
    ring
  rw [hphase]
  simp only [CBox.Contains, RBox.Contains, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_pi_div_six, Real.sin_pi_div_six]
  norm_num [phaseBase, CBox.exp, CBox.horner, CBox.squareIter, CBox.widen,
    CBox.scale, RBox.scale, CBox.mul, CBox.add, RBox.add, CBox.rat, RBox.rat,
    mulLo, mulHi, piI, piBounds, precision]
  constructor <;>
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
