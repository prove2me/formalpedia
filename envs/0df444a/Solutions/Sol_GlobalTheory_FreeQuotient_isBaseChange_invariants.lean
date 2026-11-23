-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.isBaseChange_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:24.384299+00:00
-- url     : https://prove2.me/submissions/0e04ea12-9479-423e-b9f0-00714b5440d1

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
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (h : IsFreeRingAction G A) :
    IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype := by
  cases nonempty_fintype G
  obtain ⟨s, hs, hs'⟩ := exists_galois_coordinates h
  set I := (Representation.ofDistribMulAction B G M).invariants
  have hb : Function.Bijective (I.subtype.liftBaseChange A) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun m ↦ ∑ p ∈ s, p.1 ⊗ₜ[B] moduleTrace G B M (p.2 • m), fun z ↦ ?_, fun m ↦ ?_⟩
    · induction z with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, smul_add, TensorProduct.tmul_add, Finset.sum_add_distrib] at hx hy ⊢
        rw [hx, hy]
      | tmul a x =>
        conv_rhs => rw [← sum_smul_sum_smul_eq hs hs' a, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        rw [← algebraMap_ringTrace G B A, smul_eq_mul, mul_comm, ← Algebra.smul_def,
          TensorProduct.smul_tmul]
        congr 1
        refine Subtype.ext ?_
        have hx : ∀ g : G, g • (x : M) = x := x.2
        rw [Submodule.coe_smul, ← algebraMap_smul A (ringTrace G B A _), algebraMap_ringTrace,
          Finset.sum_smul]
        simp [smul_distrib_smul, hx, mul_smul]
    · simpa using sum_smul_sum_smul_eq hs hs' m
  exact .of_equiv (LinearEquiv.ofBijective _ hb) fun x ↦
    (LinearMap.liftBaseChange_tmul A I.subtype 1 x).trans (one_smul _ _)
end GlobalTheory.FreeQuotient
