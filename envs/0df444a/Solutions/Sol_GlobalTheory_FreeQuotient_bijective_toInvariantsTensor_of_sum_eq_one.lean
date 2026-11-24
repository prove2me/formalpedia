-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.bijective_toInvariantsTensor_of_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:33:30.948824+00:00
-- url     : https://prove2.me/submissions/f1b47a85-02fe-4ba5-891a-354b208ea997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor

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
theorem _root_.solution [Fintype G] {c : A}
    (hc : ∑ g : G, g • c = 1) : Function.Bijective (toInvariantsTensor G A B N) := by
  let τ : A ⊗[B] N →ₗ[B] N := (TensorProduct.lid B N).toLinearMap ∘ₗ (ringTrace G B A).rTensor N
  have hτ : ∀ z : A ⊗[B] N, (1 : A) ⊗ₜ[B] τ z = ∑ g : G, g • z := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy, smul_add,
        Finset.sum_add_distrib]
    | tmul a n =>
      simp only [τ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, TensorProduct.smul_tmul']
      rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, algebraMap_ringTrace,
        TensorProduct.sum_tmul]
  have h1 : ringTrace G B A c = 1 :=
    FaithfulSMul.algebraMap_injective B A (by rw [algebraMap_ringTrace, hc, map_one])
  refine Function.bijective_iff_has_inverse.mpr ⟨fun z ↦ τ (c • z.1), fun n ↦ ?_, fun z ↦ ?_⟩
  · simp [τ, TensorProduct.smul_tmul', h1]
  · refine Subtype.ext ?_
    have hz : ∀ g : G, g • z.1 = z.1 := z.2
    rw [coe_toInvariantsTensor, hτ]
    simp only [smul_distrib_smul, hz]
    rw [← Finset.sum_smul, hc, one_smul]
end GlobalTheory.FreeQuotient
