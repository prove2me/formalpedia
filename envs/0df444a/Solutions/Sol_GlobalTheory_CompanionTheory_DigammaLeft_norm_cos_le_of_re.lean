-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLeft.norm_cos_le_of_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:19.919798+00:00
-- url     : https://prove2.me/submissions/93d85d85-e258-4100-a31c-679b63e85831

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegion
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_sq_norm_sin
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_sq_norm_cos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLeft
namespace GlobalTheory.CompanionTheory.DigammaLeft
theorem _root_.solution (z : ℂ) (k : ℤ) (h : z.re = Real.pi * ((k : ℝ) / 2 + 1 / 4)) :
    ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  have h2 : Real.cos (2 * z.re) = 0 := by
    have : 2 * z.re = (k : ℝ) * Real.pi + Real.pi / 2 := by rw [h]; ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero]
  have h3 : Real.cos z.re ^ 2 = Real.sin z.re ^ 2 := by
    have := Real.cos_sq' z.re
    rw [Real.cos_two_mul] at h2
    nlinarith
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs, h3]
  nlinarith [sq_nonneg (Real.sin z.re), sq_nonneg (Real.sinh z.im)]
end GlobalTheory.CompanionTheory.DigammaLeft
