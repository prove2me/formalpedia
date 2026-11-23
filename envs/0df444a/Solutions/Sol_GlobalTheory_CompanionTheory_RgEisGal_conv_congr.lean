-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.conv_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:46.197947+00:00
-- url     : https://prove2.me/submissions/2bc268af-9f1c-415b-9769-d9bc17337063

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
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution {Γ P : Subgroup G} {f f' : G → ℝ} (h : Conv Γ P f') (e : ∀ g, f g = f' g) :
    Conv Γ P f := by
  have : f = f' := funext e
  rwa [this]
end GlobalTheory.CompanionTheory.RgEisGal
