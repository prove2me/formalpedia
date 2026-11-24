-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.continuous_pt_shiftSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:42.567806+00:00
-- url     : https://prove2.me/submissions/efb182c8-c02a-41da-a14b-c724798a4114

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformVerticalInvariance
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_continuous_mk_im_shiftSnd

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
theorem _root_.solution (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  unfold pt
  exact ((continuous_mk_im_shiftSnd x.1).comp continuous_fst).prodMk ((continuous_mk_im_shiftSnd x.2).comp continuous_snd)
end GlobalTheory.CompanionTheory.TubeFourier
