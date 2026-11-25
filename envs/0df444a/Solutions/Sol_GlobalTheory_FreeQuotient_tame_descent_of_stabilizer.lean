-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.tame_descent_of_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:41.427468+00:00
-- url     : https://prove2.me/submissions/8a0fc91e-17e1-48c0-8990-bb0e6ec7b809

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_tame_descent

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
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
open scoped Pointwise
namespace GlobalTheory.FreeQuotient
theorem _root_.solution [Module.Finite A M] [Module.Projective A M]
    (h : ∀ P : Ideal A, P.IsMaximal → (Nat.card (MulAction.stabilizer G P) : A) ∉ P)
    (hM : ∀ P : Ideal A, P.IsMaximal → ∀ g ∈ MulAction.stabilizer G P, ∀ m : M,
      g • m - m ∈ P • (⊤ : Submodule A M)) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype ∧
      Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants := by
  refine tame_descent B M (fun P hP hmem ↦ h P hP ?_)
    fun P hP g hg ↦ hM P hP g (Ideal.inertia_le_stabilizer P hg)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (Ideal.inertia_le_stabilizer (M := G) P)
  rw [hk, Nat.cast_mul]
  exact P.mul_mem_right _ hmem
end GlobalTheory.FreeQuotient
