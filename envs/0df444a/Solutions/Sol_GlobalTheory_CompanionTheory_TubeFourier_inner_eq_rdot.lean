-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.inner_eq_rdot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:47.958571+00:00
-- url     : https://prove2.me/submissions/97aaeb6e-ed47-48b3-bfde-e68fe9ee8241

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
theorem _root_.solution (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = rdot (planeCoord v) (planeCoord w) := by
  rw [planeCoord_apply, planeCoord_apply]
  simp [rdot, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
end GlobalTheory.CompanionTheory.TubeFourier
