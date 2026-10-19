-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardSchemeNineteenNorm.schemePiConjugate_comp_schemePi
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:59:35.320328+00:00
-- url     : https://prove2.me/submissions/b9bb10a8-a35d-447d-b4c7-1cd28330e9de

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two explicit endomorphisms of the same rational Picard
scheme have both composites equal to scalar nineteen. This establishes
the actual scheme norm identity; isogeny properties and degrees remain
separate obligations. Named downstream consumer: nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Definitions.Def_MazurTransfer_Order13ActualTwoAffineOpenCover
import Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondSchemeCyclotomic_actualPicardOverHom_ext_field_points
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePiConjugate_geometric_composite_nineteen

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance schemeNineteenNormReverseSchemeGroupObject20261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem solution :
    schemePiConjugate ≫ schemePi = (𝟙 (Over.mk actualPicard.toBase)) ^ 19 := by
  apply MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.actualPicardOverHom_ext_field_points
  intro K _ _ _ a
  letI : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
  let 𝒱 := GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K
  simpa only [MonObj.comp_pow, Category.comp_id, Category.assoc] using
    schemePiConjugate_geometric_composite_nineteen K 𝒱 a


#print axioms solution
