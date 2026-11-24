-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.InvLine.integrable_exp_neg_abs_plane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:40.901036+00:00
-- url     : https://prove2.me/submissions/d8a8a2d9-9ad7-4e70-b650-80df2e71bc18

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformHolomorphicLines
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_exp_neg_mul_abs


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
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ × ℝ => Real.exp (-c * |t.1|) * Real.exp (-c * |t.2|)) :=
  (integrable_exp_neg_mul_abs hc).mul_prod (integrable_exp_neg_mul_abs hc)
end GlobalTheory.CompanionTheory.TubeFourier.InvLine
