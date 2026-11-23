-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.finite_and_projective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:24.42753+00:00
-- url     : https://prove2.me/submissions/2acffc6d-e77c-4ef1-b3d5-e6d5c6ad743d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime

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
theorem _root_.solution (h : IsFreeRingAction G A) :
    Module.Finite B A ∧ Module.Projective B A := by
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  have hcomp : Fintype.linearCombination B (fun p : s ↦ p.1.1) ∘ₗ
      LinearMap.pi (fun p : s ↦ ringTrace G B A ∘ₗ LinearMap.mulLeft B p.1.2) = LinearMap.id := by
    refine LinearMap.ext fun a ↦ ?_
    have := sum_smul_sum_smul_eq hs hs' a
    rw [← Finset.sum_coe_sort] at this
    simpa [Fintype.linearCombination_apply, Algebra.smul_def, mul_comm] using this
  exact ⟨.of_surjective (Fintype.linearCombination B (fun p : s ↦ p.1.1)) fun x ↦ ⟨_, LinearMap.congr_fun hcomp x⟩, .of_split _ _ hcomp⟩
end GlobalTheory.FreeQuotient
