-- Prove2me | solution 1 for GlobalTheory.smul_tensorNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:35.160292+00:00
-- url     : https://prove2.me/submissions/addf771a-e23c-426d-8f80-d1336b7ba111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_piTensorDistribMulAction_smul_tprod
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
variable [SMulDistribClass G A M]
namespace GlobalTheory
theorem _root_.solution [Finite G] [Module.Invertible A M] (κ : ι ≃ G) (x : M) (g : G) :
    letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
    g • tensorNorm A κ x = tensorNorm A κ x := by
  conv_rhs => rw [← tensorNorm_eq_of_equiv A (κ.trans (Equiv.mulLeft g)) κ x]
  rw [tensorNorm, piTensorDistribMulAction_smul_tprod]
  simp [tensorNorm, mul_smul]
end GlobalTheory
