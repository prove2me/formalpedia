-- Prove2me | solution 1 for MazurTransfer.Order13ActualIntegralPicardFamilyBaseChanges.actual_integral_picard_family_baseChanges
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T07:34:22.808341+00:00
-- url     : https://prove2.me/submissions/43303afa-2e38-4de5-b3cd-7c781953e5ba

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual integral Picard representing scheme has
compatible original Picard representations after every algebra base change;
its smoothness, properness and geometric connectedness persist.
Named downstream consumer: rational/mod-3/mod-5 fibres of this same family.
No identification with independently selected field Picards is assumed.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardRepresentation_actual_integral_picard_representation
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    ∃ D : RelativePic0Designation R (curveToBase R),
      Nonempty (RepresentsRelSubPic (curveToBase R)
        (Order13IntegralSections.positiveInfinitySection R)
        (algEquivZeroCut (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (RepresentsRelSubPic (baseChange R (curveToBase R) A)
          (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R))
          (algEquivZeroCut (baseChange R (curveToBase R) A)
            (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase := by
  obtain ⟨D, ⟨h⟩, hs,hp,hg⟩ :=
    Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation R h104
  refine ⟨D, ⟨h⟩, hs,hp,hg, ?_⟩
  intro A _ _
  letI := hs
  letI := hp
  letI := hg
  obtain ⟨hA,_⟩ := exists_representsRelSubPic_baseChange R (curveToBase R)
    (Order13IntegralSections.positiveInfinitySection R) D h A
  exact ⟨⟨hA⟩, inferInstance, inferInstance, inferInstance⟩
#print axioms solution
