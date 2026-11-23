-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelBasic.support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:40.956403+00:00
-- url     : https://prove2.me/submissions/2a54f38f-a744-4a1f-84a7-595624123fee

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOfCompact
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelBasic_finite_of_compact

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
    (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)).Finite := by
  refine (finite_of_compact X hφ (isCompact_singleton (x := x))
    (isCompact_singleton (x := y))).subset ?_
  intro γ h
  exact ⟨x, rfl, y, rfl, h⟩
end GlobalTheory.CompanionTheory.KernelBasic
