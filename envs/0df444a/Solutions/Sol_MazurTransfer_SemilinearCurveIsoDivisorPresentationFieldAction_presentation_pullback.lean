-- Prove2me | solution 1 for MazurTransfer.SemilinearCurveIsoDivisorPresentationFieldAction.presentation_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T13:35:47.561204+00:00
-- url     : https://prove2.me/submissions/424890e4-e67e-4c07-bc2f-8be49d4afec7

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: transport a complete divisor presentation under inverse
curve-isomorphism pullback when its generic-stalk and place actions match
an explicit semilinear automorphism; every original premise is retained.
Named downstream consumer: actual order-thirteen geometric Galois divisor
presentations and Picard divisor-class Galois compatibility.
The complete original FLT presentation predicate and isomorphism transport
are reused through the registered original presentation interface. -/
import Definitions.Def_MazurTransfer_SemilinearDivisorPresentationRestrictionSectionMapOriginalData20261018
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.SemilinearDivisorPresentationRestrictionFieldAction
namespace MazurTransfer.SemilinearCurveDivisorPresentationProofHelpers20261018
section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_image_lSpaceOn_iff (g : SemilinearAut K F) (S : Set (Place K F))
    (D : Divisor K F) (f : F) :
    g • f ∈ lSpaceOn ((fun v : Place K F => g • v) '' S) (g • D) ↔ f ∈ lSpaceOn S D := by
  rw [mem_lSpaceOn_iff_ord, mem_lSpaceOn_iff_ord]
  have hz : g • f = 0 ↔ f = 0 :=
    map_eq_zero_iff (SemilinearAut.toRingAut g) (SemilinearAut.toRingAut g).injective
  constructor
  · intro h v hv
    have H := h (g • v) ⟨v, hv, rfl⟩
    simpa only [hz, SemilinearAut.divisor_smul_apply_smul, SemilinearAut.ord_smul] using H
  · rintro h _ ⟨v, hv, rfl⟩
    simpa only [hz, SemilinearAut.divisor_smul_apply_smul, SemilinearAut.ord_smul] using h v hv

theorem image_lSpaceOn (g : SemilinearAut K F) (S : Set (Place K F)) (D : Divisor K F) :
    (SemilinearAut.toRingAut g) '' (lSpaceOn S D : Set F) =
      (lSpaceOn ((fun v : Place K F => g • v) '' S) (g • D) : Set F) := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_image_lSpaceOn_iff g S D a).mpr ha
  · intro hf
    refine ⟨(SemilinearAut.toRingAut g).symm f, ?_, (SemilinearAut.toRingAut g).apply_symm_apply f⟩
    apply (mem_image_lSpaceOn_iff g S D ((SemilinearAut.toRingAut g).symm f)).mp
    change (SemilinearAut.toRingAut g) ((SemilinearAut.toRingAut g).symm f) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hf

end
section
variable {C : Scheme.{u}} [IsIntegral C]

instance imageNonempty (f : C ⟶ C) [IsOpenImmersion f] (U : C.Opens) [Nonempty U] :
    Nonempty (f ''ᵁ U) := by
  obtain ⟨x⟩ := ‹Nonempty U›
  exact ⟨⟨f x.1, ⟨x.1, x.2, rfl⟩⟩⟩

theorem germToFunctionField_appIso_inv (f : C ⟶ C) [IsOpenImmersion f]
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

end
section
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K))
variable (f : C ⟶ C) [IsOpenImmersion f] (g : letI := (baseToFunctionField c).toAlgebra; SemilinearAut K C.functionField)
  (L : C.Modules) (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
  (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))

include c in
theorem presentation_restrict
    (h : IsPresentation c L D φ)
    (hfield : letI := (baseToFunctionField c).toAlgebra; ∀ (U : C.Opens) [Nonempty U] (a : Γ(C, U)),
      (SemilinearAut.toRingAut g) (algebraMap Γ(C, f ''ᵁ U) C.functionField ((f.appIso U).inv a)) =
        algebraMap Γ(C, U) C.functionField a)
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens, placesOf c U =
      (fun v : Place K C.functionField => g • v) '' placesOf c (f ''ᵁ U)) :
    letI := (baseToFunctionField c).toAlgebra
    IsPresentation c (L.restrict f) (g • D) (restrictionSectionMap c f g L φ) := by
  letI := (baseToFunctionField c).toAlgebra
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U V hVU hV m
    letI := hV
    change (SemilinearAut.toRingAut g) (φ (f ''ᵁ V) ((L.restrictAppIso f V).hom
      ((L.restrict f).presheaf.map (homOfLE hVU).op m))) =
        (SemilinearAut.toRingAut g) (φ (f ''ᵁ U) ((L.restrictAppIso f U).hom m))
    rw [Scheme.Modules.map_restrictAppIso_hom_apply]
    exact congrArg (SemilinearAut.toRingAut g) (h.nat _ _ (f.image_mono hVU) inferInstance _)
  · intro U hU a m
    letI := hU
    change (SemilinearAut.toRingAut g) (φ (f ''ᵁ U) ((L.restrictAppIso f U).hom (a • m))) =
      algebraMap Γ(C, U) C.functionField a * (SemilinearAut.toRingAut g) (φ (f ''ᵁ U) ((L.restrictAppIso f U).hom m))
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply, h.smul, map_mul, hfield]
  · intro U hU
    letI := hU
    exact (SemilinearAut.toRingAut g).injective.comp ((h.inj (f ''ᵁ U) inferInstance).comp
      (ConcreteCategory.bijective_of_isIso (L.restrictAppIso f U).hom).1)
  · intro U hU hne
    letI := hne
    have hs : Function.Surjective (L.restrictAppIso f U).hom :=
      (ConcreteCategory.bijective_of_isIso (L.restrictAppIso f U).hom).2
    change Set.range (((SemilinearAut.toRingAut g) ∘ φ (f ''ᵁ U)) ∘ (L.restrictAppIso f U).hom) = _
    rw [hs.range_comp, Set.range_comp, h.range _ (hU.image_of_isOpenImmersion f) inferInstance,
      MazurTransfer.SemilinearCurveDivisorPresentationProofHelpers20261018.image_lSpaceOn, ← hplaces]

end
section
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
variable (g : letI := (baseToFunctionField c).toAlgebra; SemilinearAut K C.functionField)

theorem places_image_of_preimage
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens,
      placesOf c (e.inv ⁻¹ᵁ U) =
        (fun v : Place K C.functionField => g • v) '' placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ U : C.Opens, placesOf c U =
      (fun v : Place K C.functionField => g • v) '' placesOf c (e.inv ''ᵁ U) := by
  letI := (baseToFunctionField c).toAlgebra
  intro U
  have h := hplaces (e.inv ''ᵁ U)
  rw [e.inv.preimage_image_eq U] at h
  exact h

end
end MazurTransfer.SemilinearCurveDivisorPresentationProofHelpers20261018
open MazurTransfer.SemilinearCurveDivisorPresentationProofHelpers20261018
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
variable (g : letI := (baseToFunctionField c).toAlgebra; SemilinearAut K C.functionField)

theorem solution (L : C.Modules)
    (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))
    (h : IsPresentation c L D φ)
    (hgeneric : letI := (baseToFunctionField c).toAlgebra; C.fromSpecStalk (genericPoint C) ≫ e.inv =
      Spec.map (CommRingCat.ofHom (SemilinearAut.toRingAut g).toRingHom) ≫ C.fromSpecStalk (genericPoint C))
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens,
      placesOf c (e.inv ⁻¹ᵁ U) =
        (fun v : Place K C.functionField => g • v) '' placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∃ ψ : ∀ U : C.Opens, Γ((Scheme.Modules.pullback e.inv).obj L, U) →+ (C.functionField : Type u),
      IsPresentation c ((Scheme.Modules.pullback e.inv).obj L) (g • D) ψ := by
  letI := (baseToFunctionField c).toAlgebra
  have hr := MazurTransfer.SemilinearCurveDivisorPresentationProofHelpers20261018.presentation_restrict c e.inv g L D φ h
    (fun U _ a => MazurTransfer.SemilinearCurveDivisorPresentationProofHelpers20261018.germToFunctionField_appIso_inv
      e.inv (CommRingCat.ofHom (SemilinearAut.toRingAut g).toRingHom) hgeneric U a)
    (places_image_of_preimage c e g hplaces)
  exact ⟨_, IsPresentation.of_iso ((Scheme.Modules.restrictFunctorIsoPullback e.inv).app L).symm hr⟩

#print axioms solution
