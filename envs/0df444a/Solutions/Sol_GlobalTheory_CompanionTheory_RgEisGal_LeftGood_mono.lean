-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.LeftGood_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:54.869645+00:00
-- url     : https://prove2.me/submissions/0fb9294d-56a8-48b9-a5cb-2d9ea4943593

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
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X} {a a' : ℝ}
    (hf : LeftGood f a) (h : a' ≤ a) : LeftGood f a' :=
  ⟨hf.1.mono fun _ hz => lt_of_lt_of_le hz h, fun b c hc => hf.2 b c (lt_of_lt_of_le hc h)⟩
end GlobalTheory.CompanionTheory.RgEisGal
