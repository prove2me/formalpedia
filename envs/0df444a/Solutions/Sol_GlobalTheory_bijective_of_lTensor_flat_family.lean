-- Prove2me | solution 1 for GlobalTheory.bijective_of_lTensor_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:15.504776+00:00
-- url     : https://prove2.me/submissions/e0c8f77b-1d80-4439-95d4-61daa3291fa3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamily
import Theorems.Thm_GlobalTheory_subsingleton_of_lTensor_flat_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type)
    [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) →
    (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) →
    (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  intro R _ N N' _ _ _ _ f J B _ _ hflat hmax hbij
  constructor
  · set K := LinearMap.ker f
    have hK : ∀ i, Subsingleton (B i ⊗[R] K) := by
      intro i
      have hinjK : Function.Injective (K.subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap K.subtype K.injective_subtype
      have hz : (f.lTensor (B i)).comp (K.subtype.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : f ∘ₗ K.subtype = 0 := by
          ext x
          exact LinearMap.mem_ker.mp x.2
        rw [this, LinearMap.lTensor_zero]
      refine ⟨fun a b => hinjK ((hbij i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax K hK
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.eq_bot_of_subsingleton
  · set q := (LinearMap.range f).mkQ
    have hQ : ∀ i, Subsingleton (B i ⊗[R] (N' ⧸ LinearMap.range f)) := by
      intro i
      have hsurj : Function.Surjective (q.lTensor (B i)) :=
        LinearMap.lTensor_surjective (B i) (Submodule.mkQ_surjective _)
      have hz : (q.lTensor (B i)).comp (f.lTensor (B i)) = 0 := by
        rw [← LinearMap.lTensor_comp]
        have : q ∘ₗ f = 0 := by
          ext x
          simp [q]
        rw [this, LinearMap.lTensor_zero]
      refine subsingleton_of_forall_eq 0 fun y => ?_
      obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := (hbij i).2 z
      rw [← LinearMap.comp_apply, hz]
      rfl
    have := subsingleton_of_lTensor_flat_family R J B hflat hmax _ hQ
    have htop : LinearMap.range f = ⊤ :=
      Submodule.unique_quotient_iff_eq_top.mp ⟨uniqueOfSubsingleton 0⟩
    exact LinearMap.range_eq_top.mp htop
end GlobalTheory
