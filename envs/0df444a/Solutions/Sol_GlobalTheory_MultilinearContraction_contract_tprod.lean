-- Prove2me | solution 1 for GlobalTheory.MultilinearContraction.contract_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:19:51.219367+00:00
-- url     : https://prove2.me/submissions/0dee6673-c9a4-4eb0-8b06-20f3c42ef40d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply
import Theorems.Thm_GlobalTheory_MultilinearContraction_contractMultilinear_apply
import Theorems.Thm_GlobalTheory_MultilinearContraction_contract_def
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.MultilinearContraction.contractMultilinear_apply

set_option autoImplicit false
open scoped TensorProduct BigOperators
open GlobalTheory GlobalTheory.MultilinearContraction
variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
namespace GlobalTheory.MultilinearContraction
theorem _root_.solution (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contract φ j (⨂ₜ[R] i, x i) = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := by
  rw [contract_def, PiTensorProduct.lift.tprod, contractMultilinear_apply]
end GlobalTheory.MultilinearContraction
