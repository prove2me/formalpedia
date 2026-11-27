-- Prove2me | solution 1 for GlobalTheory.tensorNorm_smul_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:36.099663+00:00
-- url     : https://prove2.me/submissions/f0cf6403-310a-4cd2-951a-ebe6a54fe309

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_tensorNorm_eq_of_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
omit [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution [Finite G] [Module.Invertible A M] (κ : ι ≃ G) (g : G) (x : M) :
    tensorNorm A κ (g • x) = tensorNorm A κ x := by
  rw [← tensorNorm_eq_of_equiv A (κ.trans (Equiv.mulRight g)) κ x]
  simp [tensorNorm, mul_smul]
end GlobalTheory
