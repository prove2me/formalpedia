-- Prove2me | solution 1 for GlobalTheory.isLeftCoaction_iff_isCoaction_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:51.040395+00:00
-- url     : https://prove2.me/submissions/ec0f9e39-b2e0-4ce0-a3be-c076a4214066

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Theorems.Thm_GlobalTheory_IsCoaction_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra
open GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution [IsCocomm R C] (ρ : M →ₗ[R] C ⊗[R] M) :
    IsLeftCoaction ρ ↔ IsCoaction ((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ) := by

  let e : C ⊗[R] (C ⊗[R] M) ≃ₗ[R] M ⊗[R] (C ⊗[R] C) :=
    (TensorProduct.assoc R C C M).symm ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ
      (TensorProduct.comm R C C).lTensor M
  have h1 : ∀ t : C ⊗[R] M, e (ρ.lTensor C t) = TensorProduct.assoc R M C C
      (((TensorProduct.comm R C M).toLinearMap ∘ₗ ρ).rTensor C (TensorProduct.comm R C M t)) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m =>
      simp only [LinearMap.lTensor_tmul, comm_tmul, LinearMap.rTensor_tmul, LinearMap.comp_apply,
        LinearEquiv.coe_coe]
      generalize ρ m = s
      induction s with
      | zero => simp
      | add a b ha hb => simp only [map_add, tmul_add, add_tmul, ha, hb]
      | tmul c' m' => simp [e]
  have h2 : ∀ t : C ⊗[R] M,
      e (TensorProduct.assoc R C C M ((comul : C →ₗ[R] C ⊗[R] C).rTensor M t)) =
      (comul : C →ₗ[R] C ⊗[R] C).lTensor M (TensorProduct.comm R C M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp [e]
  have h3 : ∀ t : C ⊗[R] M, TensorProduct.comm R R M ((Coalgebra.counit : C →ₗ[R] R).rTensor M t) =
      (Coalgebra.counit : C →ₗ[R] R).lTensor M (TensorProduct.comm R C M t) := by
    intro t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c m => simp
  constructor
  · intro h
    refine ⟨fun m => ?_, fun m => ?_⟩
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h1, ← h2, h.coassoc]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← h3, h.counit, comm_tmul]
  · intro h
    refine ⟨fun m => e.injective ?_, fun m => (TensorProduct.comm R R M).injective ?_⟩
    · rw [h1, h2]; exact (h.coassoc m).symm
    · rw [h3, comm_tmul]; exact h.counit m
end GlobalTheory
