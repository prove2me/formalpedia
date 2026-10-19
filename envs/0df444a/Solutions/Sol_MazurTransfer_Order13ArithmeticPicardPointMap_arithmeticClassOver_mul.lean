-- Prove2me | solution 1 for MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_mul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T17:26:11.874009+00:00
-- url     : https://prove2.me/submissions/1c6841c1-d1fc-49a4-9b31-81585ff91088

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_presentationTensorPrincipal_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original arithmetic class map on represented Picard points preserves multiplication. Named downstream consumer: rationalClassEquiv and rational Picard norm-kernel comparison.
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
namespace MazurTransfer.ArithmeticPicardOverHomMulProofHelpers20261018
section QuotientComparison
variable {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]
theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]
theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F) = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]
end QuotientComparison
end MazurTransfer.ArithmeticPicardOverHomMulProofHelpers20261018
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem solution :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase,
      arithmeticClassOver K 𝒱 ε D h (a * b) =
        arithmeticClassOver K 𝒱 ε D h a + arithmeticClassOver K 𝒱 ε D h b := by
  let hG : RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D := h
  letI := hG.grpObj
  intro a b
  let pa := pointOfOverHom K D a
  let pb := pointOfOverHom K D b
  let pab := pointOfOverHom K D (a * b)
  obtain ⟨Ea, φa, ha⟩ :=
    MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h pa
  obtain ⟨Eb, φb, hb⟩ :=
    MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h pb
  obtain ⟨Eab, φab, hab⟩ :=
    MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h pab
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso hG a b
  let i' : pointLineBundle (curveToBase K) ε D h pab ≅
      pointLineBundle (curveToBase K) ε D h pa ⊗ pointLineBundle (curveToBase K) ε D h pb :=
    (Scheme.Modules.pullback (toProdSpec (curveToBase K))).mapIso i ≪≫
      Scheme.Modules.pullbackTensorObjIso (toProdSpec (curveToBase K)) _ _
  have hp := hab.of_iso i'.symm
  have hP := MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase
    (curveToBase K) (actual_constantsAreBase_good_characteristic K)
    (pointLineBundle (curveToBase K) ε D h pa) (pointLineBundle (curveToBase K) ε D h pb)
    (pointLineBundle_isInvertible (curveToBase K) ε D h pa)
    (pointLineBundle_isInvertible (curveToBase K) ε D h pb)
    Ea.1 Eb.1 Eab.1 φa ha.nat ha.smul ha.inj ha.range φb hb.nat hb.smul hb.inj hb.range
    (fun U => (φab U).comp (Scheme.Modules.Hom.app i'.symm.hom U).hom)
    hp.nat hp.smul hp.inj hp.range
  have hcl : Pic0.mk Eab = Pic0.mk (Ea + Eb) :=
    (MazurTransfer.ArithmeticPicardOverHomMulProofHelpers20261018.pic0_mk_eq_iff Eab (Ea + Eb)).mpr ((MazurTransfer.ArithmeticPicardOverHomMulProofHelpers20261018.pic_mk_eq_iff _ _).mpr (by
      simpa only [AddSubgroup.coe_add, sub_add_eq_sub_sub] using hP))
  rw [Pic0.mk_add,
    arithmeticClass_eq_of_presentation K 𝒱 ε D h pab Eab φab hab,
    arithmeticClass_eq_of_presentation K 𝒱 ε D h pa Ea φa ha,
    arithmeticClass_eq_of_presentation K 𝒱 ε D h pb Eb φb hb] at hcl
  exact hcl


#print axioms solution
#print axioms MazurTransfer.ArithmeticPicardOverHomMulProofHelpers20261018.pic_mk_eq_iff
#print axioms MazurTransfer.ArithmeticPicardOverHomMulProofHelpers20261018.pic0_mk_eq_iff
