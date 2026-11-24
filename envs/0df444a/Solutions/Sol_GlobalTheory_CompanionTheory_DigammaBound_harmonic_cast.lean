-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.harmonic_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:15.366669+00:00
-- url     : https://prove2.me/submissions/19cc08fa-31af-42f9-a978-869bc7c45111

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
theorem _root_.solution (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]
end GlobalTheory.CompanionTheory.DigammaBound
