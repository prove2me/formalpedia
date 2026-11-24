-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.continuous_chgR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:01:31.509953+00:00
-- url     : https://prove2.me/submissions/971f5de3-0f94-4a97-9426-141163d62d44

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_continuous_affR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chgR α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_affR _ _ _).prodMk (continuous_affR _ _ _)
end GlobalTheory.CompanionTheory.RgEisGal
