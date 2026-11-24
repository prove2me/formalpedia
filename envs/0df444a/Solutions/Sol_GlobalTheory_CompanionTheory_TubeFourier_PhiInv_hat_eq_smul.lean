-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.PhiInv.hat_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:01:26.378844+00:00
-- url     : https://prove2.me/submissions/bfb20aa2-19f9-49ae-990c-657bca78d789

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunction
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_phi_eq_smul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier GlobalTheory.CompanionTheory.TubeFourier.PhiInv
namespace GlobalTheory.CompanionTheory.TubeFourier.PhiInv
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    (∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) =
      Complex.exp ((rdot x t : ℝ) : ℂ) • phi G x t := by
  rw [phi_eq_smul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
end GlobalTheory.CompanionTheory.TubeFourier.PhiInv
