-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.add_half_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:03.073047+00:00
-- url     : https://prove2.me/submissions/fee4f565-5baf-4258-a6ec-843181f66d52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset
namespace GlobalTheory.CompanionTheory.DigammaBound
theorem _root_.solution (z : ℂ) (hz : 1 / 2 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    x + 1 / 2 ≤ ‖z + (x : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (z + (x : ℂ))
  have h2 : (z + (x : ℂ)).re = z.re + x := by simp
  rw [h2] at h
  have := le_abs_self (z.re + x)
  linarith
end GlobalTheory.CompanionTheory.DigammaBound
