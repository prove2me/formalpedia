-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.InvLine.dot_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:40.145608+00:00
-- url     : https://prove2.me/submissions/28a29c1d-6612-4826-8194-27d32afde5f2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLines

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.InvLine
namespace GlobalTheory.CompanionTheory.TubeFourier.InvLine
theorem _root_.solution (p v : ℂ × ℂ) (τ : ℂ) (t : ℝ × ℝ) :
    dot (p + τ • v) t = dot p t + τ * dot v t := by
  simp [dot]
  ring
end GlobalTheory.CompanionTheory.TubeFourier.InvLine
