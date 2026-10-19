-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_mul
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:40:48.073992+00:00
-- url     : https://prove2.me/submissions/677f6b8c-0e4c-4002-9b6b-5f18850887ee

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: multiplication of geometric points of the SAME original
rational represented Picard adds their intrinsic actual divisor classes.
Named downstream consumer: injectivity of geometric arithmetic classes and
detection of the actual diamond scheme norm identities.
Original MazurTheorem Order13ActualPicardGeometricArithmeticGroup proof;
official Anthropic FLT Poincare tensor inputs at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticGroupData
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_presentationTensorPrincipal_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13ActualPicardGeometricArithmeticGroup
open MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition
open MazurTransfer.Order13GeometricRelativeCurveChange
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open scoped CategoryTheory.MonObj
namespace MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017
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

end MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)

theorem geometricGroupAdditionBundleInvertible20261017
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Scheme.Modules.IsInvertible (actualGeometricPointLineBundle K a) :=
  geometricPointLineBundle_isInvertible (curveToBase ℚ) infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K) a

theorem solution :
    letI := (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
      (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
    ∀ a b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase,
      geometricArithmeticClassOver K 𝒱 (a * b) =
        geometricArithmeticClassOver K 𝒱 a + geometricArithmeticClassOver K 𝒱 b := by
  let hG : RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard := actualRepresentation
  letI := hG.grpObj
  intro a b
  let pa := pointOfOverHom K a
  let pb := pointOfOverHom K b
  let pab := pointOfOverHom K (a * b)
  obtain ⟨Ea, φa, ha⟩ :=
    MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 pa
  obtain ⟨Eb, φb, hb⟩ :=
    MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 pb
  obtain ⟨Eab, φab, hab⟩ :=
    MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 pab
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso hG a b
  let i' : actualGeometricPointLineBundle K pab ≅
      actualGeometricPointLineBundle K pa ⊗ actualGeometricPointLineBundle K pb :=
    (Scheme.Modules.pullback (geometricCurveEmbedding K)).mapIso i ≪≫
      Scheme.Modules.pullbackTensorObjIso (geometricCurveEmbedding K) _ _
  have hp := hab.of_iso i'.symm
  have hP := MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase
    (curveToBase K) (actual_constantsAreBase_good_characteristic K)
    (actualGeometricPointLineBundle K pa) (actualGeometricPointLineBundle K pb)
    (geometricGroupAdditionBundleInvertible20261017 K pa)
    (geometricGroupAdditionBundleInvertible20261017 K pb)
    Ea.1 Eb.1 Eab.1 φa ha.nat ha.smul ha.inj ha.range φb hb.nat hb.smul hb.inj hb.range
    (fun U => (φab U).comp (Scheme.Modules.Hom.app i'.symm.hom U).hom)
    hp.nat hp.smul hp.inj hp.range
  have hcl : Pic0.mk Eab = Pic0.mk (Ea + Eb) :=
    (MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017.pic0_mk_eq_iff Eab (Ea + Eb)).mpr ((MazurTransfer.GeometricArithmeticGroupAdditionQuotientHelpers20261017.pic_mk_eq_iff _ _).mpr (by
      simpa only [AddSubgroup.coe_add, sub_add_eq_sub_sub] using hP))
  rw [Pic0.mk_add,
    geometricArithmeticClass_eq_of_presentation K 𝒱 pab Eab φab hab,
    geometricArithmeticClass_eq_of_presentation K 𝒱 pa Ea φa ha,
    geometricArithmeticClass_eq_of_presentation K 𝒱 pb Eb φb hb] at hcl
  exact hcl


#print axioms solution
