-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.rankAtStalk_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:37.562055+00:00
-- url     : https://prove2.me/submissions/55539b4f-76ea-4bb3-859a-f148f90db328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_finite_and_projective

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
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (h : IsFreeRingAction G A) (p : PrimeSpectrum B) :
    Module.rankAtStalk A p = Nat.card G := by
  cases nonempty_fintype G
  haveI := (finite_and_projective B h).1
  haveI := (finite_and_projective B h).2
  obtain ⟨q, rfl⟩ := Algebra.IsIntegral.comap_surjective B A p
  haveI : Nontrivial A := q.nontrivial
  rw [← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_of_equiv (galoisEquiv B h).toLinearEquiv,
    Module.rankAtStalk_eq_finrank_of_free]
  simp
end GlobalTheory.FreeQuotient
