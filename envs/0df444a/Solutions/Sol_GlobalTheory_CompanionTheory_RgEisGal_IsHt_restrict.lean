-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.IsHt_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:54.040167+00:00
-- url     : https://prove2.me/submissions/05c48ae8-7f96-4c65-ad5e-696a4e8aed2d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GalleryOfTubesAndCrossing

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
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {Γ K P Q : Subgroup G} {η : G → ℝ} (h : IsHt Γ K Q η) (hPQ : P ≤ Q) :
    IsHt Γ K P η :=
  ⟨fun p hp g => h.left p (hPQ hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hPQ hp), h.cont⟩
end GlobalTheory.CompanionTheory.RgEisGal
