-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.isHt_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:32.842929+00:00
-- url     : https://prove2.me/submissions/a5eaca13-1d5d-41dc-8937-d87a3c3ce3b8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G]
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution {Γ K P P' : Subgroup G} {η : G → ℝ} (h : IsHt Γ K P η) (hP : P' ≤ P) : IsHt Γ K P' η :=
  ⟨fun p hp g => h.left p (hP hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hP hp), h.cont⟩
end GlobalTheory.CompanionTheory.RgEis
