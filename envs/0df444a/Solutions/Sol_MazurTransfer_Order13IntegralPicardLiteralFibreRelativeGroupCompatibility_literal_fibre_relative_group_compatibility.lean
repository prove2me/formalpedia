-- Prove2me | solution 1 for MazurTransfer.Order13IntegralPicardLiteralFibreRelativeGroupCompatibility.literal_fibre_relative_group_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T08:16:12.28853+00:00
-- url     : https://prove2.me/submissions/bedde9af-a9da-49b1-9175-1f8cc82861b0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal curve fibres retain the original integral Picard
family's relative multiplication, via its genuine base-change representation
and pointed whole-curve isomorphism. Named downstream consumer: the same
family's arithmetic divisor-class group and torsion specialization.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
import Theorems.Thm_MazurTransfer_CurveIsoPicardPointMultiplicationTransport_transport_representation_relative_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open MazurTransfer.CurveIsoPicardRepresentationTransport
open MazurTransfer.CurveIsoPicardPointMultiplicationTransport
open scoped CategoryTheory.MonObj
theorem solution
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    ∃ hS : RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroCut (curveToBase S) (positiveInfinitySection S))
      (literalFibreDesignation R S D),
      letI := (show RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
        (algEquivZeroGroupCut (curveToBase S) (positiveInfinitySection S)).toSubPicCondition
          (literalFibreDesignation R S D) from hS).grpObj
      ∃ Θ : (Over.mk (𝟙 (Spec (.of S))) ⟶ Over.mk (literalFibreDesignation R S D).toBase) ≃
          SchemeHomOver (specMap R S) D.toBase,
        (∀ a, (Θ a).val = a.left ≫ pullback.fst D.toBase (specMap R S)) ∧
        ∀ a b, Θ (a * b) =
          (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
            (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
              D from h).relativeGroupLaw.mul (specMap R S) (Θ a) (Θ b) := by
  obtain ⟨hB,hP⟩ := exists_representsRelSubPic_baseChange R (curveToBase R)
    (positiveInfinitySection R) D h S
  let hBG : RepresentsRelSubPic (baseChange R (curveToBase R) S)
      (sectionBaseChange S (positiveInfinitySection R))
      (algEquivZeroGroupCut (baseChange R (curveToBase R) S)
        (sectionBaseChange S (positiveInfinitySection R))).toSubPicCondition (D.baseChange S) := hB
  letI := hBG.grpObj
  obtain ⟨Θ,hcoe,hmul,_⟩ := baseChange_points_mul_poincare_compat R (curveToBase R)
    (positiveInfinitySection R) D h S hB hP
  have hmul0 : ∀ x y : SchemeHomOver (𝟙 (Spec (.of S))) (D.baseChange S).toBase,
      Θ (schemeHomOverToOverHom (hBG.relativeGroupLaw.mul (𝟙 _) x y)) =
        (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
          (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
            D from h).relativeGroupLaw.mul (specMap R S)
              (Θ (schemeHomOverToOverHom x)) (Θ (schemeHomOverToOverHom y)) := by
    intro x y
    simpa only [RepresentsRelSubPic.relativeGroupLaw,relativeGroupLawOfGrpObj_mul,
      schemeHomOverToOverHom_overHomToSchemeHomOver] using
        hmul (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  let hS := transportRepresentation (literalCurveFibreIso R S)
    (literalCurveFibreIso_over R S) (literalCurveFibreIso_section R S) (D.baseChange S) hB
  let hSG : RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroGroupCut (curveToBase S) (positiveInfinitySection S)).toSubPicCondition
        (literalFibreDesignation R S D) := hS
  refine ⟨hS,?_⟩
  letI := hSG.grpObj
  refine ⟨Θ,hcoe,?_⟩
  intro a b
  have heq : schemeHomOverToOverHom
      (hBG.relativeGroupLaw.mul (𝟙 _) (overHomToSchemeHomOver a)
        (overHomToSchemeHomOver b)) = a * b := by
    apply Over.OverMorphism.ext
    exact transport_representation_relative_mul (literalCurveFibreIso R S)
      (literalCurveFibreIso_over R S) (literalCurveFibreIso_section R S)
      (D.baseChange S) hB (𝟙 _) (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  have hm := hmul0 (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  rw [heq] at hm
  exact hm
#print axioms solution
