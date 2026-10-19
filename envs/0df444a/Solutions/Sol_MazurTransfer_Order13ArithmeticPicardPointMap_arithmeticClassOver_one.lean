-- Prove2me | solution 1 for MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T17:20:59.78938+00:00
-- url     : https://prove2.me/submissions/569045ad-8520-40f1-861c-085e7938bbc4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original arithmetic class map on represented Picard points sends the identity to zero. Named downstream consumer: rationalClassEquiv and rational Picard norm-kernel comparison.
-/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.LineBundleFieldComparison MazurTransfer.Order13ArithmeticPicardPointMap
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj
namespace MazurTransfer.ArithmeticPicardOverHomOneProofHelpers20261018
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem pointLineBundle_over_one_iso_unit :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    Nonempty (pointLineBundle (curveToBase K) ε D h (pointOfOverHom K D 1) ≅
      𝟙_ (curveScheme K).Modules) := by
  let hG : RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D := h
  letI := hG.grpObj
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  exact ⟨(Scheme.Modules.pullback (toProdSpec (curveToBase K))).mapIso i ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (toProdSpec (curveToBase K))⟩

end MazurTransfer.ArithmeticPicardOverHomOneProofHelpers20261018

theorem solution (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D) :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    arithmeticClassOver K 𝒱 ε D h 1 = 0 := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  obtain ⟨e⟩ := MazurTransfer.ArithmeticPicardOverHomOneProofHelpers20261018.pointLineBundle_over_one_iso_unit K ε D h
  obtain ⟨φ, _, hnat, hsmul, hinj, hrange⟩ :=
    Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
  have hp : IsPresentation (curveToBase K) (𝟙_ (curveScheme K).Modules) 0 φ :=
    ⟨hnat, hsmul, hinj, hrange⟩
  have hz := arithmeticClass_eq_of_presentation K 𝒱 ε D h (pointOfOverHom K D 1) 0
    (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) (hp.of_iso e)
  exact hz.symm.trans Pic0.mk_zero
#print axioms solution
#print axioms MazurTransfer.ArithmeticPicardOverHomOneProofHelpers20261018.pointLineBundle_over_one_iso_unit
