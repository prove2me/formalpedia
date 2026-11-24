-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstantTestRepresentation_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:11.02572+00:00
-- url     : https://prove2.me/submissions/727368bd-e517-426a-b81a-4f0f6c193170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Theorems.Thm_GlobalTheory_JR_WeilProd_isTestRep_tensorRep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y] (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ), IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f → (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  first | exact @GlobalTheory.JR.WeilProd.isTestRep_tensorRep | exact GlobalTheory.JR.WeilProd.isTestRep_tensorRep | (intros; apply GlobalTheory.JR.WeilProd.isTestRep_tensorRep <;> assumption)
end _root_.GlobalTheory.T
