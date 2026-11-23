-- Prove2me | solution 1 for GlobalTheory.MultilinearContraction.prodMultilinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:52.546364+00:00
-- url     : https://prove2.me/submissions/8bc81273-0bae-4ab5-955d-9f8ed4e2ed90

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
theorem _root_.solution (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodMultilinear φ x = ∏ i, φ i (x i) := rfl
end GlobalTheory.MultilinearContraction
