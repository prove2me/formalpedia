-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.bijective_toInvariantsTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:01:58.640321+00:00
-- url     : https://prove2.me/submissions/c2265ca4-8c24-4d4a-9173-7d9d6373f9fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_exists_sum_smul_eq_one_of_free
import Theorems.Thm_GlobalTheory_FreeQuotient_bijective_toInvariantsTensor_of_sum_eq_one

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
variable (G : Type*) [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass B G A]
  (N : Type*) [AddCommGroup N] [Module B N]
variable [SMulCommClass G B A]
variable [FaithfulSMul B A] [Algebra.IsInvariant B A G]
variable {G A}
namespace GlobalTheory.FreeQuotient
theorem _root_.solution [Finite G] (h : IsFreeRingAction G A) :
    Function.Bijective (toInvariantsTensor G A B N) := by
  cases nonempty_fintype G
  obtain ⟨c, hc⟩ := exists_sum_smul_eq_one_of_free h
  exact bijective_toInvariantsTensor_of_sum_eq_one B N hc
end GlobalTheory.FreeQuotient
