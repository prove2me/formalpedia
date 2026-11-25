-- Prove2me | solution 1 for GlobalTheory.forall_smul_eq_iff_tensorNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:20.587524+00:00
-- url     : https://prove2.me/submissions/21debfd9-33a9-4e81-8ecb-8f95695994ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_invertible_of_bijective_toSpanSingleton
import Theorems.Thm_GlobalTheory_forall_smul_eq_iff_of_invariant_generator
import Theorems.Thm_GlobalTheory_piTensorDistribMulAction_smulDistribClass
import Theorems.Thm_GlobalTheory_smul_tensorNorm
import Theorems.Thm_GlobalTheory_bijective_toSpanSingleton_tensorNorm

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
variable {A}
namespace GlobalTheory
theorem _root_.solution [Finite G] (κ : ι ≃ G) {e : M}
    (he : Function.Bijective (LinearMap.toSpanSingleton A M e)) (y : ⨂[A] _ : ι, M) :
    letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
    (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • tensorNorm A κ e :=
  letI := piTensorDistribMulAction G A (fun _ : ι ↦ M)
  haveI := piTensorDistribMulAction_smulDistribClass G A (fun _ : ι ↦ M)
  haveI := invertible_of_bijective_toSpanSingleton he
  forall_smul_eq_iff_of_invariant_generator (bijective_toSpanSingleton_tensorNorm κ he)
    (smul_tensorNorm A κ e) y
end GlobalTheory
