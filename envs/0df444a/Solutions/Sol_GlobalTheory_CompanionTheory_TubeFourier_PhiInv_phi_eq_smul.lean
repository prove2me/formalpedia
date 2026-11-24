-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.PhiInv.phi_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:41:32.119044+00:00
-- url     : https://prove2.me/submissions/d3236d24-8542-430b-a37a-935c08ea9d79

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialFourierIntegralBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformRecoversFunction
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_PhiInv_dot_pt_eq

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
    phi G x t = Complex.exp (-((rdot x t : ℝ) : ℂ)) •
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y) := by
  unfold phi
  rw [← integral_smul]
  congr 1
  funext y
  rw [smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring
end GlobalTheory.CompanionTheory.TubeFourier.PhiInv
