-- Prove2me | solution 1 for GlobalTheory.T.digamma_log_bound_left_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:45.108886+00:00
-- url     : https://prove2.me/submissions/648fffe0-6693-46fc-9c33-8a05f735ffc9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegion
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlaneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundLeftRegionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLeft_norm_digamma_le_left


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re ≤ 1 / 4 → (1 / 2 ≤ |w.im| ∨ ∃ k : ℤ, w.re = (k : ℝ) / 2 + 1 / 4) → ‖Complex.digamma w‖ ≤ C * Real.log (‖w‖ + 2) := by
  first | exact @GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left | exact GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left | (intros; apply GlobalTheory.CompanionTheory.DigammaLeft.norm_digamma_le_left <;> assumption)
end _root_.GlobalTheory.T
