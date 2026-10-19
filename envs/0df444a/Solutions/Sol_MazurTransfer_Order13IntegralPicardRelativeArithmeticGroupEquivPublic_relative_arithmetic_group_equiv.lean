-- Prove2me | solution 1 for MazurTransfer.Order13IntegralPicardRelativeArithmeticGroupEquivPublic.relative_arithmetic_group_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T08:35:37.4308+00:00
-- url     : https://prove2.me/submissions/a7d9772b-35a0-46cd-a9c3-203bf63e8924

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original integral Picard representation's relative
points over a perfect field carry the actual arithmetic degree-zero
divisor-class group, with the original relative multiplication.
Consumes the exact native mirror of our publicly accepted arithmetic
group proof to permit assembly with the accepted finite-field count.
Named downstream consumer: same-family rational and finite-field groups
in the order-13 torsion specialization argument.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
import Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRelativeGroupCompatibility_literal_fibre_relative_group_compatibility
import Theorems.Thm_MazurTransfer_PicardRepresentationPointComparison_overPointEquiv_mul
import Theorems.Thm_MazurTransfer_order13_actual_arithmetic_picard_group_equivalence
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open MazurTransfer.Order13IntegralPicardLiteralFibreRelativeGroupCompatibility
open MazurTransfer.PicardRepresentationPointComparison
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open scoped CategoryTheory.MonObj
theorem solution
    (R K : Type u) [CommRing R] [Field K] [PerfectField K] [Algebra R K]
    (h104 : IsUnit (104 : R)) (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    letI : Fact ((104 : K) ≠ 0) := ⟨by
      have hh : IsUnit (104 : K) := by simpa only [map_ofNat] using h104.map (algebraMap R K)
      exact hh.ne_zero⟩
    letI := (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
        D from h).relativeGroupLaw.pointGroup (specMap R K)
    Nonempty (SchemeHomOver (specMap R K) D.toBase ≃*
      Multiplicative (Pic0 K (actualCurveFunctionField K)))  := by
  have hh : IsUnit (104 : K) := by simpa only [map_ofNat] using h104.map (algebraMap R K)
  letI : Fact ((104 : K) ≠ 0) := ⟨hh.ne_zero⟩
  letI := (show RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
    (algEquivZeroGroupCut (curveToBase R) (positiveInfinitySection R)).toSubPicCondition
      D from h).relativeGroupLaw.pointGroup (specMap R K)
  obtain ⟨hK,hΘ⟩ := literal_fibre_relative_group_compatibility R K D h
  let hKG : RepresentsRelSubPic (curveToBase K) (positiveInfinitySection K)
      (algEquivZeroGroupCut (curveToBase K) (positiveInfinitySection K)).toSubPicCondition
      (literalFibreDesignation R K D) := hK
  letI := hKG.grpObj
  obtain ⟨Θ,_,hmul⟩ := hΘ
  let ΘG : (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (literalFibreDesignation R K D).toBase) ≃*
      SchemeHomOver (specMap R K) D.toBase := { Θ with map_mul' := hmul }
  obtain ⟨D0,h0,⟨A⟩⟩ := MazurTransfer.order13_actual_arithmetic_picard_group_equivalence
    K hh.ne_zero (positiveInfinitySection K)
  let h0G : RepresentsRelSubPic (curveToBase K) (positiveInfinitySection K)
      (algEquivZeroGroupCut (curveToBase K) (positiveInfinitySection K)).toSubPicCondition D0 := h0
  letI := h0G.grpObj
  let E : (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (literalFibreDesignation R K D).toBase) ≃*
      (Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk D0.toBase) :=
    { overPointEquiv hK h0 (𝟙 _) with
      map_mul' := by
        intro a b
        exact overPointEquiv_mul
          (P := algEquivZeroGroupCut (curveToBase K) (positiveInfinitySection K)) hKG h0G a b }
  exact ⟨ΘG.symm.trans (E.trans A)⟩

#print axioms solution
