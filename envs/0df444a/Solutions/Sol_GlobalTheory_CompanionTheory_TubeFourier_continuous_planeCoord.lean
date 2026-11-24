-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.continuous_planeCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:47:35.188681+00:00
-- url     : https://prove2.me/submissions/1a49d4a8-3899-40d9-a53f-194aa4559fc0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionProd
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_planeCoord_apply

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
open scoped FourierTransform
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution : Continuous planeCoord := by
  rw [show (planeCoord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun v => (v 0, v 1) from funext planeCoord_apply]
  fun_prop
end GlobalTheory.CompanionTheory.TubeFourier
