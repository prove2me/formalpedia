-- Prove2me | solution 1 for GlobalTheory.T.digamma_log_bound_right_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:01.143847+00:00
-- url     : https://prove2.me/submissions/def655af-d995-43dc-877d-a01517f85b7c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_digamma_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  first | exact @GlobalTheory.CompanionTheory.DigammaBound.digamma_bound | exact GlobalTheory.CompanionTheory.DigammaBound.digamma_bound | (intros; apply GlobalTheory.CompanionTheory.DigammaBound.digamma_bound <;> assumption)
end _root_.GlobalTheory.T
