-- Prove2me | solution 1 for MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClassOver_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T18:05:58.25356+00:00
-- url     : https://prove2.me/submissions/4e2042a2-f46e-4e37-8e0a-eddef8878bb0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_one
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClassOver_mul
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_represented_picard_field_points_classify_line_bundles
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_nonempty_iso_tensorUnit_of_principal_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard and divisor interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original arithmetic divisor-class map on Over-category points is injective. Named downstream consumer: the original rational Picard class-group equivalence and transport of actual rational norm kernels.
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
namespace MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018
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

theorem arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    arithmeticClass K 𝒱 ε D h a = 0 ↔
      Nonempty (pointLineBundle (curveToBase K) ε D h a ≅ 𝟙_ (curveScheme K).Modules) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  constructor
  · intro ha
    obtain ⟨E, φ, hp⟩ :=
      MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a
    have hmk : Pic0.mk E = Pic0.mk 0 := by
      rw [Pic0.mk_zero, arithmeticClass_eq_of_presentation K 𝒱 ε D h a E φ hp, ha]
    have hP : Divisor.IsPrincipal E.1 := by
      have hp0 := (MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.pic_mk_eq_iff E.1 0).mp ((MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.pic0_mk_eq_iff E 0).mp hmk)
      simpa only [sub_zero] using hp0
    exact MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
      (curveToBase K) 𝒱 (pointLineBundle (curveToBase K) ε D h a)
      (pointLineBundle_isInvertible (curveToBase K) ε D h a)
      (((MazurTransfer.represented_picard_field_points_classify_line_bundles (curveToBase K) ε D h).1 a).2 𝒱) E.1 φ hp hP
  · rintro ⟨e⟩
    obtain ⟨φ, _, hnat, hsmul, hinj, hrange⟩ :=
      Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
    have hp : IsPresentation (curveToBase K) (𝟙_ (curveScheme K).Modules) 0 φ :=
      ⟨hnat, hsmul, hinj, hrange⟩
    have hpN := hp.of_iso e
    have hz := arithmeticClass_eq_of_presentation K 𝒱 ε D h a 0
      (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) hpN
    exact hz.symm.trans Pic0.mk_zero

theorem arithmeticClassOver_eq_zero_iff_eq_one :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase,
      arithmeticClassOver K 𝒱 ε D h a = 0 ↔ a = 1 := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  intro a
  constructor
  · intro ha
    obtain ⟨ia⟩ := (MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit K 𝒱 ε D h _).mp ha
    obtain ⟨i1⟩ := MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.pointLineBundle_over_one_iso_unit K ε D h
    have hp := ((MazurTransfer.represented_picard_field_points_classify_line_bundles (curveToBase K) ε D h).2.1
      (pointOfOverHom K D a) (pointOfOverHom K D 1)).mp ⟨ia ≪≫ i1.symm⟩
    exact Over.OverMorphism.ext (congrArg Subtype.val hp)
  · rintro rfl
    exact arithmeticClassOver_one K 𝒱 ε D h

end MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem solution : Function.Injective (arithmeticClassOver K 𝒱 ε D h) := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  intro a b hab
  have h4 : arithmeticClassOver K 𝒱 ε D h (b * b⁻¹) = 0 := by
    rw [mul_inv_cancel, arithmeticClassOver_one K 𝒱 ε D h]
  have h3 : arithmeticClassOver K 𝒱 ε D h (a * b⁻¹) = 0 := by
    rw [arithmeticClassOver_mul K 𝒱 ε D h] at h4 ⊢
    rw [hab]
    exact h4
  have h1 := (MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.arithmeticClassOver_eq_zero_iff_eq_one K 𝒱 ε D h _).mp h3
  exact mul_inv_eq_one.mp h1


#print axioms solution
#print axioms MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.pic_mk_eq_iff
#print axioms MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.pic0_mk_eq_iff
#print axioms MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.pointLineBundle_over_one_iso_unit
#print axioms MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit
#print axioms MazurTransfer.ArithmeticPicardOverHomInjectivityProofHelpers20261018.arithmeticClassOver_eq_zero_iff_eq_one
