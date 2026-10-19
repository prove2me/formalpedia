-- Prove2me | solution 1 for MazurTransfer.Order13ActualIntegralAbelianPicardFamily.actual_integral_abelian_picard_family
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T07:50:41.526987+00:00
-- url     : https://prove2.me/submissions/0ac1643b-2a6d-412f-b48c-4c48dbabde99

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual integral Picard family carries a commutative
relative group law, is an abelian scheme in the original interface, and
has an Abel-Jacobi morphism based at the actual positive infinity section.
The same representing scheme has Picard representations after all algebra
base changes. Named downstream consumer: arithmetic good reduction of the
rational order-13 Jacobian through this single integral family.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardFamilyBaseChanges_actual_integral_picard_family_baseChanges
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_smooth_relative_dimension_one
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    ∃ (D : RelativePic0Designation R (curveToBase R))
      (_ : RepresentsRelSubPic (curveToBase R)
        (Order13IntegralSections.positiveInfinitySection R)
        (algEquivZeroCut (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)) D)
      (L : RelativeGroupLaw R D.toBase)
      (aj : SchemeHomOver (curveToBase R) D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (.of R)))).val = D.zeroSection ∧
      (Order13IntegralSections.positiveInfinitySection R).val ≫ aj.val = D.zeroSection ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (RepresentsRelSubPic (baseChange R (curveToBase R) A)
          (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R))
          (algEquivZeroCut (baseChange R (curveToBase R) A)
            (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase := by
  letI : IsProper (curveToBase R) := MazurTransfer.order13_actual_integral_curve_proper R
  letI : SmoothOfRelativeDimension 1 (curveToBase R) :=
    MazurTransfer.order13_actual_integral_curve_smooth_relative_dimension_one R h104
  letI : GeometricallyIntegral (curveToBase R) :=
    MazurTransfer.order13_actual_integral_curve_geometrically_integral R h104
  obtain ⟨D, ⟨h⟩, hs,hp,hg,hA⟩ :=
    Order13ActualIntegralPicardFamilyBaseChanges.actual_integral_picard_family_baseChanges R h104
  obtain ⟨L,aj,hb,hc,h1,haj,_⟩ :=
    exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic.{u,u} R
      (curveToBase R) (Order13IntegralSections.positiveInfinitySection R) D h hs hp hg
  exact ⟨D,h,L,aj,hb,hc,h1,haj,hA⟩
#print axioms solution
