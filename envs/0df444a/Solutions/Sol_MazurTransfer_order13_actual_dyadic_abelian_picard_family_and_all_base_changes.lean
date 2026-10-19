-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_abelian_picard_family_and_all_base_changes
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T08:14:12.131096+00:00
-- url     : https://prove2.me/submissions/45b4d056-8f20-4ab8-97cb-1cec05a1e71b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual dyadic abelian Picard family and its compatible representations after every algebra base change.
Named downstream consumer: the actual dyadic Neron model and norm extensions.
-/
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_integral_picard_representation_original
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
namespace MazurTransfer.Order13ActualDyadicMixedPicardFamilyBaseChanges
theorem actual_dyadic_integral_picard_family_baseChanges :
    ∃ D : RelativePic0Designation BaseRing (curveToBase BaseRing),
      Nonempty (RepresentsRelSubPic (curveToBase BaseRing)
        (zeroSection)
        (algEquivZeroCut (curveToBase BaseRing) (zeroSection)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      ∀ (A : Type) [CommRing A] [Algebra BaseRing A],
        Nonempty (RepresentsRelSubPic (baseChange BaseRing (curveToBase BaseRing) A)
          (sectionBaseChange A (zeroSection))
          (algEquivZeroCut (baseChange BaseRing (curveToBase BaseRing) A)
            (sectionBaseChange A (zeroSection)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase := by
  obtain ⟨D, ⟨h⟩, hs,hp,hg⟩ :=
    MazurTransfer.order13_actual_dyadic_integral_picard_representation_original
  refine ⟨D, ⟨h⟩, hs,hp,hg, ?_⟩
  intro A _ _
  letI := hs
  letI := hp
  letI := hg
  obtain ⟨hA,_⟩ := exists_representsRelSubPic_baseChange BaseRing (curveToBase BaseRing)
    (zeroSection) D h A
  exact ⟨⟨hA⟩, inferInstance, inferInstance, inferInstance⟩


end MazurTransfer.Order13ActualDyadicMixedPicardFamilyBaseChanges
namespace MazurTransfer.Order13ActualDyadicMixedAbelianPicardFamily
theorem actual_dyadic_integral_abelian_picard_family :
    ∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (_ : RepresentsRelSubPic (curveToBase BaseRing)
        (zeroSection)
        (algEquivZeroCut (curveToBase BaseRing) (zeroSection)) D)
      (L : RelativeGroupLaw BaseRing D.toBase)
      (aj : SchemeHomOver (curveToBase BaseRing) D.toBase),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (.of BaseRing)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (.of BaseRing)))).val = D.zeroSection ∧
      (zeroSection).val ≫ aj.val = D.zeroSection ∧
      ∀ (A : Type) [CommRing A] [Algebra BaseRing A],
        Nonempty (RepresentsRelSubPic (baseChange BaseRing (curveToBase BaseRing) A)
          (sectionBaseChange A (zeroSection))
          (algEquivZeroCut (baseChange BaseRing (curveToBase BaseRing) A)
            (sectionBaseChange A (zeroSection)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase := by
  obtain ⟨_,_,hP,hD,hG,-⟩ :=
    Order13ActualDyadicMixedFiniteMapData.actual_dyadic_picard_geometry_and_finite_map_inputs
  letI : IsProper (curveToBase BaseRing) := hP
  letI : SmoothOfRelativeDimension 1 (curveToBase BaseRing) := hD
  letI : GeometricallyIntegral (curveToBase BaseRing) := hG
  obtain ⟨D, ⟨h⟩, hs,hp,hg,hA⟩ :=
    Order13ActualDyadicMixedPicardFamilyBaseChanges.actual_dyadic_integral_picard_family_baseChanges
  obtain ⟨L,aj,hb,hc,h1,haj,_⟩ :=
    exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.{0,0} BaseRing
      (curveToBase BaseRing) (zeroSection) D h hs hp hg
  exact ⟨D,h,L,aj,hb,hc,h1,haj,hA⟩


end MazurTransfer.Order13ActualDyadicMixedAbelianPicardFamily
theorem solution : (∃ D : RelativePic0Designation BaseRing (curveToBase BaseRing),
      Nonempty (RepresentsRelSubPic (curveToBase BaseRing)
        (zeroSection)
        (algEquivZeroCut (curveToBase BaseRing) (zeroSection)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      ∀ (A : Type) [CommRing A] [Algebra BaseRing A],
        Nonempty (RepresentsRelSubPic (baseChange BaseRing (curveToBase BaseRing) A)
          (sectionBaseChange A (zeroSection))
          (algEquivZeroCut (baseChange BaseRing (curveToBase BaseRing) A)
            (sectionBaseChange A (zeroSection)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase) ∧ (∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (_ : RepresentsRelSubPic (curveToBase BaseRing)
        (zeroSection)
        (algEquivZeroCut (curveToBase BaseRing) (zeroSection)) D)
      (L : RelativeGroupLaw BaseRing D.toBase)
      (aj : SchemeHomOver (curveToBase BaseRing) D.toBase),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (.of BaseRing)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (.of BaseRing)))).val = D.zeroSection ∧
      (zeroSection).val ≫ aj.val = D.zeroSection ∧
      ∀ (A : Type) [CommRing A] [Algebra BaseRing A],
        Nonempty (RepresentsRelSubPic (baseChange BaseRing (curveToBase BaseRing) A)
          (sectionBaseChange A (zeroSection))
          (algEquivZeroCut (baseChange BaseRing (curveToBase BaseRing) A)
            (sectionBaseChange A (zeroSection)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase) := by
  exact ⟨MazurTransfer.Order13ActualDyadicMixedPicardFamilyBaseChanges.actual_dyadic_integral_picard_family_baseChanges, MazurTransfer.Order13ActualDyadicMixedAbelianPicardFamily.actual_dyadic_integral_abelian_picard_family⟩
#print axioms solution
