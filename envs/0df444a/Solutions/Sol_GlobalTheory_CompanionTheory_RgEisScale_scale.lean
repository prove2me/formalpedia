-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisScale.scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:44:10.740858+00:00
-- url     : https://prove2.me/submissions/9ee1ddc2-cf88-4d1b-bac0-55ee14a57c7e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EisensteinScalingLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisScale_wall_scale

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisScale
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisScale
theorem _root_.solution : PositivityTheory.RgEis.Scale := by
  intro G _ _ _ _ _ W _ _ _ K ρ _ _ Γ P P' c η η' β l s hs hl hW
  obtain ⟨R, D, Op, H, hw⟩ := hW
  exact ⟨_, _, _, _, wall_scale hs hl hw⟩
end GlobalTheory.CompanionTheory.RgEisScale
