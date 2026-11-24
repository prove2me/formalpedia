-- Prove2me | solution 1 for GlobalTheory.MultilinearContraction.prodForm_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:41.524079+00:00
-- url     : https://prove2.me/submissions/7e14f8bb-3e26-467e-a409-de85657778ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct BigOperators
open GlobalTheory GlobalTheory.MultilinearContraction
variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
namespace GlobalTheory.MultilinearContraction
theorem _root_.solution (φ : ∀ i, X i →ₗ[R] R) :
    prodForm φ = PiTensorProduct.lift (prodMultilinear φ) := rfl
end GlobalTheory.MultilinearContraction
