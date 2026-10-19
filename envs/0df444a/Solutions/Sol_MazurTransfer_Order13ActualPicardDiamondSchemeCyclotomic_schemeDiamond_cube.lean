-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.schemeDiamond_cube
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:01:11.755166+00:00
-- url     : https://prove2.me/submissions/c23603d6-bc4f-4902-b893-97610e8d3628

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: cyclotomic and hyperelliptic identities are equalities of
endomorphisms of the SAME existing rational Picard scheme, using reduced
source and separated target and every residue-field point.
Named downstream consumer: actual nineteen-norm scheme endomorphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondGroupActionExplicitConstructorFacts20261017
import Definitions.Def_MazurTransfer_Order13ActualTwoAffineOpenCover
import Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondSchemeCyclotomic_actualPicardOverHom_ext_field_points
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricDiamondGroupAction_schemeDiamond_geometric_cube

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open scoped CategoryTheory.MonObj
local instance schemeDiamondCubeGroupObject20261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj

theorem solution :
    schemeDiamond ≫ schemeDiamond ≫ schemeDiamond =
      (𝟙 (Over.mk actualPicard.toBase))⁻¹ := by
  apply MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.actualPicardOverHom_ext_field_points
  intro K _ _ _ a
  letI : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
  let 𝒱 := GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K
  simpa only [GrpObj.comp_inv, Category.comp_id, Category.assoc] using
    schemeDiamond_geometric_cube K 𝒱 a


#print axioms solution
