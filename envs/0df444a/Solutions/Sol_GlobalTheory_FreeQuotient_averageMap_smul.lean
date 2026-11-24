-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.averageMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:33:27.895104+00:00
-- url     : https://prove2.me/submissions/c898c6c2-3394-4a0a-b5df-407cb8f4f021

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_averageMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] [Fintype G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  {N : Type*} [AddCommGroup N] [Module A N] [DistribMulAction G N] [SMulDistribClass G A N]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (f : M →ₗ[A] N) (h : G) (m : M) :
    averageMap G f (h • m) = h • averageMap G f m := by
  simp only [averageMap_apply, Finset.smul_sum, smul_smul]
  rw [← Equiv.sum_comp (Equiv.mulLeft h)]
  simp
end GlobalTheory.FreeQuotient
