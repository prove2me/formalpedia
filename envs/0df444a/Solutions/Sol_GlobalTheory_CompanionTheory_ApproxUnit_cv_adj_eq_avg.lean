-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ApproxUnit.cv_adj_eq_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:22.703586+00:00
-- url     : https://prove2.me/submissions/8e9391f2-04f7-4c2f-8081-2bb9577f7448

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CvAdjEqAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ApproxUnit
namespace GlobalTheory.CompanionTheory.ApproxUnit
theorem _root_.solution (X : Ctx) (f ψ : X.G → ℂ) (hψ : IsBump X ψ) (y : X.G) :
    cv X.μ (adj ψ) f y = ∫ z, f (z⁻¹ * y) * ((‖ψ z⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h : adj ψ z = ((‖ψ z⁻¹‖ : ℝ) : ℂ) := by
    unfold adj
    rw [hψ.2.1 z⁻¹]
    simp
  simp only [h]
  ring
end GlobalTheory.CompanionTheory.ApproxUnit
