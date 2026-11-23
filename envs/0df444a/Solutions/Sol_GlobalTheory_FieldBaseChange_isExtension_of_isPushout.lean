-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isExtension_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:10.168878+00:00
-- url     : https://prove2.me/submissions/5e6694a5-452c-433b-a4ba-13ffddc1ecc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra F B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [IsScalarTower K F B] [H : Algebra.IsPushout K F A B]
    (a : A →ₛₗ[algebraMap K F] B) (ha : ∀ x, a x = algebraMap A B x) : IsExtension a := by
  have hb : ∀ (c : F) (v : A), H.out.equiv (c ⊗ₜ v) = c • a v := by
    intro c v
    rw [IsBaseChange.equiv_tmul, ha]
    rfl
  refine ⟨?_, fun ℓ => ?_⟩
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := H.out.equiv.surjective y
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c v => rw [hb]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
    | add s t hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
  · refine ⟨(TensorProduct.lid K A).toLinearMap.toAddMonoidHom.comp
      ((TensorProduct.map ℓ LinearMap.id).toAddMonoidHom.comp
        H.out.equiv.symm.toLinearMap.toAddMonoidHom), fun c v => ?_⟩
    show TensorProduct.lid K A (TensorProduct.map ℓ LinearMap.id (H.out.equiv.symm (c • a v))) = ℓ c • v
    rw [← hb, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      LinearMap.id_apply]
end GlobalTheory.FieldBaseChange
