-- Prove2me | solution 1 for GlobalTheory.MultilinearContraction.contractMultilinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:47:51.328241+00:00
-- url     : https://prove2.me/submissions/d1e305cb-1bed-4936-b96d-33ef56db92b6

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
variable {ι : Type*} [Fintype ι] [dι : DecidableEq ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]
namespace GlobalTheory.MultilinearContraction
theorem _root_.solution (φ : ∀ i, X i →ₗ[R] R) (j : ι) (x : ∀ i, X i) :
    contractMultilinear φ j x = (∏ i ∈ Finset.univ.erase j, φ i (x i)) • x j := rfl
end GlobalTheory.MultilinearContraction
