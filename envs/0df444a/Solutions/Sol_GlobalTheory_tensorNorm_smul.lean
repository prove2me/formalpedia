-- Prove2me | solution 1 for GlobalTheory.tensorNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:48.149857+00:00
-- url     : https://prove2.me/submissions/02935033-e6fc-4759-91db-5ba39b7a4f94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

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
theorem _root_.solution [Fintype G] (κ : ι ≃ G) (a : A) (x : M) :
    tensorNorm A κ (a • x) = (∏ g : G, g • a) • tensorNorm A κ x := by
  letI : Fintype ι := .ofEquiv _ κ.symm
  simp only [tensorNorm, smul_distrib_smul]
  rw [MultilinearMap.map_smul_univ, Equiv.prod_comp κ (fun g ↦ g • a)]
end GlobalTheory
