-- Prove2me | solution 1 for MazurTransfer.DivisorPresentationRestrictionPublic.presentation_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:42:50.418073+00:00
-- url     : https://prove2.me/submissions/6799ec8b-15df-4cc3-b40e-d8fa64f83afe

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: divisor presentations transport along an open-immersion
restriction when the generic field action and open-place sets agree.
Named downstream consumer: actual diamond inverse pullback and comparison
of represented Picard points with arithmetic divisor classes.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationRestrictionSectionMapData
import Theorems.Thm_MazurTransfer_GenericCurveImageSectionMapCompatibility_germToFunctionField_appIso_inv
import Theorems.Thm_MazurTransfer_DivisorSectionSpaceFieldAction_image_lSpaceOn
noncomputable section
universe u
open MazurTransfer
open MazurTransfer.DivisorPresentationRestrictionFieldAction
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) (f : C ⟶ C) [IsOpenImmersion f]
    (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)
    (L : C.Modules) (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))
    (h : IsPresentation c L D φ)
    (hfield : ∀ (U : C.Opens) [Nonempty U] (a : Γ(C, U)),
      σ (algebraMap Γ(C, f ''ᵁ U) C.functionField ((f.appIso U).inv a)) =
        algebraMap Γ(C, U) C.functionField a)
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens, placesOf c U =
      (fun v : Place K C.functionField => σ • v) '' placesOf c (f ''ᵁ U)) :
    letI := (baseToFunctionField c).toAlgebra;
    IsPresentation c (L.restrict f) (σ • D) (restrictionSectionMap c f σ L φ) := by
  letI := (baseToFunctionField c).toAlgebra
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U V hVU hV m
    letI := hV
    change σ (φ (f ''ᵁ V) ((L.restrictAppIso f V).hom
      ((L.restrict f).presheaf.map (homOfLE hVU).op m))) =
        σ (φ (f ''ᵁ U) ((L.restrictAppIso f U).hom m))
    rw [Scheme.Modules.map_restrictAppIso_hom_apply]
    exact congrArg σ (h.nat _ _ (f.image_mono hVU) inferInstance _)
  · intro U hU a m
    letI := hU
    change σ (φ (f ''ᵁ U) ((L.restrictAppIso f U).hom (a • m))) =
      algebraMap Γ(C, U) C.functionField a * σ (φ (f ''ᵁ U) ((L.restrictAppIso f U).hom m))
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply, h.smul, map_mul, hfield]
  · intro U hU
    letI := hU
    exact σ.injective.comp ((h.inj (f ''ᵁ U) inferInstance).comp
      (ConcreteCategory.bijective_of_isIso (L.restrictAppIso f U).hom).1)
  · intro U hU hne
    letI := hne
    have hs : Function.Surjective (L.restrictAppIso f U).hom :=
      (ConcreteCategory.bijective_of_isIso (L.restrictAppIso f U).hom).2
    change Set.range ((σ ∘ φ (f ''ᵁ U)) ∘ (L.restrictAppIso f U).hom) = _
    rw [hs.range_comp, Set.range_comp, h.range _ (hU.image_of_isOpenImmersion f) inferInstance,
      DivisorSectionSpaceFieldAction.image_lSpaceOn, ← hplaces]

#print axioms solution
