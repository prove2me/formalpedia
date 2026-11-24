-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ApproxUnit.cv_eq_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:23.918971+00:00
-- url     : https://prove2.me/submissions/cd149014-2ee6-49ef-a4a2-180f3005d3a2

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
theorem _root_.solution (X : Ctx) (φ ψ : X.G → ℂ) (hψ : IsBump X ψ) (g : X.G) :
    cv X.μ φ ψ g = ∫ w, φ (g * w) * ((‖ψ w⁻¹‖ : ℝ) : ℂ) ∂X.μ := by
  unfold cv
  rw [← integral_mul_left_eq_self _ g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [mul_inv_rev, inv_mul_cancel_right]
  rw [← hψ.2.1]
end GlobalTheory.CompanionTheory.ApproxUnit
