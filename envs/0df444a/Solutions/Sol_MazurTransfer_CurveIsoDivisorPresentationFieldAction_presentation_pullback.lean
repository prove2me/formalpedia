-- Prove2me | solution 1 for MazurTransfer.CurveIsoDivisorPresentationFieldAction.presentation_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:54:32.058338+00:00
-- url     : https://prove2.me/submissions/a7a3c4d6-f315-441f-8c12-a00c900b3b90

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve pullback transports full divisor presentations
when its actual generic-stalk and place actions match a field automorphism.
Named downstream consumer: the actual order-thirteen curve over Q and the
arithmetic Picard action comparison.
-/
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Theorems.Thm_MazurTransfer_DivisorPresentationRestrictionPublic_presentation_restrict
import Theorems.Thm_MazurTransfer_GenericCurveImageSectionMapCompatibility_germToFunctionField_appIso_inv
noncomputable section
universe u
open MazurTransfer
namespace MazurTransfer.CurveIsoDivisorPresentationPullbackHelpers20261017
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
  (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)

theorem places_image_of_preimage
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens,
      placesOf c (e.inv ⁻¹ᵁ U) =
        (fun v : Place K C.functionField => σ • v) '' placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ U : C.Opens, placesOf c U =
      (fun v : Place K C.functionField => σ • v) '' placesOf c (e.inv ''ᵁ U) := by
  letI := (baseToFunctionField c).toAlgebra
  intro U
  have h := hplaces (e.inv ''ᵁ U)
  rw [e.inv.preimage_image_eq U] at h
  exact h

end MazurTransfer.CurveIsoDivisorPresentationPullbackHelpers20261017
open MazurTransfer.CurveIsoDivisorPresentationPullbackHelpers20261017
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
  (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)
theorem solution {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) (e : C ≅ C)
    (σ : letI := (baseToFunctionField c).toAlgebra; C.functionField ≃ₐ[K] C.functionField)
    (L : C.Modules)
    (D : letI := (baseToFunctionField c).toAlgebra; Divisor K C.functionField)
    (φ : ∀ U : C.Opens, Γ(L, U) →+ (C.functionField : Type u))
    (h : IsPresentation c L D φ)
    (hgeneric : C.fromSpecStalk (genericPoint C) ≫ e.inv =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ C.fromSpecStalk (genericPoint C))
    (hplaces : letI := (baseToFunctionField c).toAlgebra; ∀ U : C.Opens,
      placesOf c (e.inv ⁻¹ᵁ U) =
        (fun v : Place K C.functionField => σ • v) '' placesOf c U) :
    letI := (baseToFunctionField c).toAlgebra;
    ∃ ψ : ∀ U : C.Opens, Γ((Scheme.Modules.pullback e.inv).obj L, U) →+ (C.functionField : Type u),
      IsPresentation c ((Scheme.Modules.pullback e.inv).obj L) (σ • D) ψ := by
  letI := (baseToFunctionField c).toAlgebra
  have hr := DivisorPresentationRestrictionPublic.presentation_restrict c e.inv σ L D φ h
    (fun U _ a => GenericCurveImageSectionMapCompatibility.germToFunctionField_appIso_inv
      e.inv (CommRingCat.ofHom σ.toRingHom) hgeneric U a)
    (places_image_of_preimage c e σ hplaces)
  exact ⟨_, IsPresentation.of_iso ((Scheme.Modules.restrictFunctorIsoPullback e.inv).app L).symm hr⟩

#print axioms solution
