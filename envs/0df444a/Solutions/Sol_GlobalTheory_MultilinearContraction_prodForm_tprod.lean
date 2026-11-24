-- Prove2me | solution 1 for GlobalTheory.MultilinearContraction.prodForm_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:52.233407+00:00
-- url     : https://prove2.me/submissions/eae353dc-1cbe-40cc-92cc-6888f778217a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply
import Theorems.Thm_GlobalTheory_MultilinearContraction_prodMultilinear_apply
import Theorems.Thm_GlobalTheory_MultilinearContraction_prodForm_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.MultilinearContraction.prodMultilinear_apply

set_option autoImplicit false
open scoped TensorProduct BigOperators
open GlobalTheory GlobalTheory.MultilinearContraction
variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
namespace GlobalTheory.MultilinearContraction
theorem _root_.solution (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodForm φ (⨂ₜ[R] i, x i) = ∏ i, φ i (x i) := by
  rw [prodForm_def, PiTensorProduct.lift.tprod, prodMultilinear_apply]
end GlobalTheory.MultilinearContraction
