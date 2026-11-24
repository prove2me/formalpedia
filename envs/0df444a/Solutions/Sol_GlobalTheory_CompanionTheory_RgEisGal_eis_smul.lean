-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.eis_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:58:49.430095+00:00
-- url     : https://prove2.me/submissions/9def40e4-e83d-444c-9071-c7db846ba6b1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StripEntireOfFac

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
theorem _root_.solution (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (s : ℂ)
    (w : W) : eis Γ K P c ρ Λ g (s • w) = s • eis Γ K P c ρ Λ g w := by
  simp only [eis, map_smul]
  rw [← tsum_const_smul'' s]
  congr 1
  ext q
  rw [smul_comm]
end GlobalTheory.CompanionTheory.RgEisGal
