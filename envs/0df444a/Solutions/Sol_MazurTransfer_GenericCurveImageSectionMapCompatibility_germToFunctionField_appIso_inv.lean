-- Prove2me | solution 1 for MazurTransfer.GenericCurveImageSectionMapCompatibility.germToFunctionField_appIso_inv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:03:12.380758+00:00
-- url     : https://prove2.me/submissions/c1618f58-65a0-4fcb-9873-7b46d968348f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: generic field action agrees with the inverse section
isomorphism on image opens. Named downstream consumer: scalar compatibility
in the restriction/pullback transport of divisor presentations.
-/
import Mathlib
noncomputable section
universe u
namespace MazurTransfer.GenericCurveImageSectionMapCompatibility
open CategoryTheory AlgebraicGeometry
variable {C : Scheme.{u}} [IsIntegral C]

instance imageNonempty (f : C ⟶ C) [IsOpenImmersion f] (U : C.Opens) [Nonempty U] :
    Nonempty (f ''ᵁ U) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  exact ⟨⟨f x.1, ⟨x.1, x.2, rfl⟩⟩⟩

end MazurTransfer.GenericCurveImageSectionMapCompatibility
open CategoryTheory AlgebraicGeometry
open MazurTransfer.GenericCurveImageSectionMapCompatibility
variable {C : Scheme.{u}} [IsIntegral C]
theorem solution (f : C ⟶ C) [IsOpenImmersion f]
    (σ : C.functionField ⟶ C.functionField)
    (hgeneric : C.fromSpecStalk (genericPoint C) ≫ f =
      Spec.map σ ≫ C.fromSpecStalk (genericPoint C))
    (U : C.Opens) [Nonempty U] (a : Γ(C, U)) :
    σ (C.germToFunctionField (f ''ᵁ U) ((f.appIso U).inv a)) =
      C.germToFunctionField U a := by
  have hU : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hW : genericPoint C ∈ f ''ᵁ U :=
    ((genericPoint_spec C).mem_open_set_iff (f ''ᵁ U).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (f ''ᵁ U)))
  have hres : Spec.map σ ≫ (f ''ᵁ U).fromSpecStalkOfMem (genericPoint C) hW =
      U.fromSpecStalkOfMem (genericPoint C) hU ≫
        f.resLE (f ''ᵁ U) U (f.preimage_image_eq U).ge := by
    apply (cancel_mono (f ''ᵁ U).ι).mp
    simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Hom.resLE_comp_ι, Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
    exact hgeneric.symm
  have hm : C.germToFunctionField (f ''ᵁ U) ≫ σ =
      (f.appIso U).hom ≫ C.germToFunctionField U := by
    apply Spec.map_injective
    simp only [Spec.map_comp]
    calc
      Spec.map σ ≫ Spec.map (C.germToFunctionField (f ''ᵁ U)) =
          Spec.map σ ≫ (f ''ᵁ U).fromSpecStalkOfMem (genericPoint C) hW ≫
            (f ''ᵁ U).toSpecΓ := by rw [Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
      _ = (U.fromSpecStalkOfMem (genericPoint C) hU ≫
            f.resLE (f ''ᵁ U) U (f.preimage_image_eq U).ge) ≫ (f ''ᵁ U).toSpecΓ := by
              rw [← Category.assoc, hres]
      _ = U.fromSpecStalkOfMem (genericPoint C) hU ≫ U.toSpecΓ ≫
            Spec.map ((f.appIso U).hom) := by
              rw [Category.assoc, Scheme.Hom.appIso_hom', ← Scheme.Opens.toSpecΓ_SpecMap_appLE]
      _ = Spec.map (C.germToFunctionField U) ≫ Spec.map ((f.appIso U).hom) := by
            rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
  have ha := congrArg (fun g : Γ(C, f ''ᵁ U) ⟶ C.functionField => g ((f.appIso U).inv a)) hm
  change σ (C.germToFunctionField (f ''ᵁ U) ((f.appIso U).inv a)) =
    C.germToFunctionField U ((f.appIso U).hom ((f.appIso U).inv a)) at ha
  have hi : (f.appIso U).hom ((f.appIso U).inv a) = a :=
    ConcreteCategory.congr_hom (f.appIso U).inv_hom_id a
  rw [hi] at ha
  exact ha

#print axioms solution
