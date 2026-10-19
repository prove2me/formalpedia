-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemeDiamond_isMonHom
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:54:17.00565+00:00
-- url     : https://prove2.me/submissions/33316a10-030d-486f-8d1d-6ab6c63d1173

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual Picard diamond and both nineteen-norm
endomorphisms are internal group morphisms, by preservation on all test
schemes. Named downstream consumer: scheme isogenies and descent kernels.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Theorems.Thm_MazurTransfer_MonoidObjectMorphismFromPointwiseGroupLaw_isMonHom_of_all_points

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance actualPicardDiamondGroupMorphismProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj



local instance actualPicardDiamondGroupMorphismProvider220261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance actualPicardDiamondGroupMorphismProvider320261017 : Algebra ℚ (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField ℚ) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra ℚ
local instance actualPicardDiamondGroupMorphismProvider420261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj


namespace MazurTransfer.ActualPicardDiamondGroupMorphismHelpers20261017
theorem schemeDiamond_points_one (T : Over (Spec (CommRingCat.of ℚ))) :
    (1 : T ⟶ Over.mk actualPicard.toBase) ≫ schemeDiamond = 1 := by
  apply overHomToSchemeHomOver_injective
  change postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv)
      (actualLaw.one T.hom) = actualLaw.one T.hom
  exact actualFieldHom_one _ T.hom

theorem schemeDiamond_points_mul (T : Over (Spec (CommRingCat.of ℚ)))
    (a b : T ⟶ Over.mk actualPicard.toBase) :
    (a * b) ≫ schemeDiamond = (a ≫ schemeDiamond) * (b ≫ schemeDiamond) := by
  apply overHomToSchemeHomOver_injective
  change postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv)
      (actualLaw.mul T.hom (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) =
    actualLaw.mul T.hom
      (postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv)
        (overHomToSchemeHomOver a))
      (postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv)
        (overHomToSchemeHomOver b))
  exact actualFieldHom_mul _ T.hom _ _


end MazurTransfer.ActualPicardDiamondGroupMorphismHelpers20261017
open MazurTransfer.ActualPicardDiamondGroupMorphismHelpers20261017
theorem solution : IsMonHom schemeDiamond :=
  MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points schemeDiamond
    schemeDiamond_points_one schemeDiamond_points_mul


#print axioms solution
