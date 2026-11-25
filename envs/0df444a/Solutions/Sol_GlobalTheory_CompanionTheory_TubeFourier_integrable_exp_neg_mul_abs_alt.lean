-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_mul_abs_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:47.564504+00:00
-- url     : https://prove2.me/submissions/9cfceaba-8310-4db3-b982-651fd086f2f5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FInt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuous
import Theorems.Thm_UpperTheory_Reformulated_B_Yha4_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) :=
  _root_.UpperTheory.Reformulated.B.Yha4.main hc
end GlobalTheory.CompanionTheory.TubeFourier
