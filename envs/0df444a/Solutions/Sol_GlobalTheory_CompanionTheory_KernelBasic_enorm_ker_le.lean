-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.enorm_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:40:53.618194+00:00
-- url     : https://prove2.me/submissions/ec9f645e-f1d7-4c41-899c-8c6aaa28ce58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_support_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelBasic
namespace GlobalTheory.CompanionTheory.KernelBasic
theorem _root_.solution (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ‖ker X.Γ φ x y‖ₑ ≤ ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := by
  unfold ker
  rw [finsum_eq_sum _ (support_finite X hφ x y)]
  exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)
end GlobalTheory.CompanionTheory.KernelBasic
