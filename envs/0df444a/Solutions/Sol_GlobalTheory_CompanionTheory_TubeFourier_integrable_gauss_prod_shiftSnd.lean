-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.integrable_gauss_prod_shiftSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:44:19.15551+00:00
-- url     : https://prove2.me/submissions/ef9cc6e8-9489-46a0-8588-3ca12e1fa5e3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftGaussianDecayStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TubeTransformVerticalInvariance

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
theorem _root_.solution (K : ℝ) :
    Integrable fun y : ℝ × ℝ => K * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
  have h1 : Integrable fun x : ℝ => Real.exp (-1 * x ^ 2) := integrable_exp_neg_mul_sq one_pos
  have h2 := (h1.mul_prod h1).const_mul K
  rw [Measure.volume_eq_prod]
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 2
  ring
end GlobalTheory.CompanionTheory.TubeFourier
