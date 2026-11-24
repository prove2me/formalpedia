-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLeft.norm_cos_le_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:18.589834+00:00
-- url     : https://prove2.me/submissions/bb444af6-1207-47f9-accf-1440a7dea122

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
theorem _root_.solution (z : ℂ) (h : 1 ≤ |z.im|) : ‖Complex.cos z‖ ≤ 2 * ‖Complex.sin z‖ := by
  have h1 : 1 ≤ |Real.sinh z.im| := by
    rw [Real.abs_sinh]
    exact h.trans (Real.self_le_sinh_iff.mpr (abs_nonneg _))
  have h2 : 1 ≤ Real.sinh z.im ^ 2 := by
    rw [← sq_abs]; nlinarith
  have hc := sq_norm_cos z
  have hs := sq_norm_sin z
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, hc, hs]
  nlinarith [Real.cos_sq_le_one z.re, sq_nonneg (Real.sin z.re)]
end GlobalTheory.CompanionTheory.DigammaLeft
