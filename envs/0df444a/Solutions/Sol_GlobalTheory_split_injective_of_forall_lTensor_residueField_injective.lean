-- Prove2me | solution 1 for GlobalTheory.split_injective_of_forall_lTensor_residueField_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:51.410945+00:00
-- url     : https://prove2.me/submissions/1624b103-32d1-4a68-9a68-324ac0bc4339

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R B]
    [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ (m : Ideal R) [m.IsMaximal], Injective (l.lTensor m.ResidueField)) :
    ∃ r : C →ₗ[R] B, r ∘ₗ l = LinearMap.id := by
  have hloc : ∀ (m : Ideal R) [m.IsMaximal], Injective ((l.baseChange (Localization.AtPrime m)).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
    intro m _
    have e : (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
          (Localization.AtPrime m) m.ResidueField C) ∘
          ((l.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) =
        (l.lTensor m.ResidueField) ∘ (AlgebraTensorModule.cancelBaseChange R
          (Localization.AtPrime m) (Localization.AtPrime m) m.ResidueField B) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        (Localization.AtPrime m) (Localization.AtPrime m) (M := m.ResidueField) l) x).symm
    exact Injective.of_comp (e ▸ (h m).comp (LinearEquiv.injective _))
  have hfree : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] C) := fun m _ =>
    Module.free_of_flat_of_isLocalRing
  have hinj : Injective l := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    refine Module.subsingleton_of_localization_maximal (R := R)
      (fun m _ => Localization.AtPrime m ⊗[R] LinearMap.ker l)
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).2 (hloc m)
    have h1 : Injective (l.lTensor (Localization.AtPrime m)) :=
      HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩
    have h2 : Injective ((LinearMap.ker l).subtype.lTensor (Localization.AtPrime m)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    refine (subsingleton_iff_forall_eq 0).2 fun y => h2 (h1 ?_)
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  have : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  have : Module.FinitePresentation R (C ⧸ LinearMap.range l) :=
    Module.finitePresentation_of_surjective (LinearMap.range l).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map l)
  have : Module.Projective R (C ⧸ LinearMap.range l) := by
    refine Module.projective_of_localization_maximal' (fun m _ => Localization.AtPrime m)
      (fun m _ => Localization.AtPrime m ⊗[R] (C ⧸ LinearMap.range l))
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    have := Module.free_of_lTensor_residueField_injective
      (l.baseChange (Localization.AtPrime m))
      ((LinearMap.range l).mkQ.baseChange (Localization.AtPrime m))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _))
      (lTensor_exact _ l.exact_map_mkQ_range (Submodule.mkQ_surjective _)) (hloc m)
    infer_instance
  have := (Exact.split_tfae l.exact_map_mkQ_range hinj (Submodule.mkQ_surjective _)).out 0 1
  rw [← this]
  exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)
end GlobalTheory
