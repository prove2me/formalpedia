-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.eis_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:48.330107+00:00
-- url     : https://prove2.me/submissions/4079d8a5-3993-4365-a007-4435086f1d29

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
theorem _root_.solution {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {Λ Λ' : G → ℂ} {s s' : ℂ}
    (g : G) (w : W) (hs : s = s') (e : ∀ x, Λ x = Λ' x) :
    s • eis Γ K P c ρ Λ g w = s' • eis Γ K P c ρ Λ' g w := by
  have he : Λ = Λ' := funext e
  rw [hs, he]
end GlobalTheory.CompanionTheory.RgEisGal
