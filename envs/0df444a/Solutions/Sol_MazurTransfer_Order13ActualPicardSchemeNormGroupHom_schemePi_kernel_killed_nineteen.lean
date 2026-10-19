-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePi_kernel_killed_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:55:51.173591+00:00
-- url     : https://prove2.me/submissions/41df11a5-6309-421f-b0e1-2540677b7144

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same actual Picard diamond and both nineteen-norm
endomorphisms are internal group morphisms, by preservation on all test
schemes. Named downstream consumer: scheme isogenies and descent kernels.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData

import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNineteenNorm_schemePi_comp_schemePiConjugate

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian MazurTransfer
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondGroupAction
open MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open scoped CategoryTheory.MonObj
local instance actualPiKernelKilledNineteenProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj



local instance actualPiKernelKilledNineteenProvider220261017 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance actualPiKernelKilledNineteenProvider320261017 : Algebra ℚ (GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionField ℚ) :=
  GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel.actualCurveFunctionFieldAlgebra ℚ
local instance actualPiKernelKilledNineteenProvider420261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj


local instance originalPiPiKernelMonHom20261017 : IsMonHom schemePi := MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePi_isMonHom
local instance originalPiPiConjugateKernelMonHom20261017 : IsMonHom schemePiConjugate := MazurTransfer.Order13ActualPicardSchemeNormGroupHom.schemePiConjugate_isMonHom
theorem solution (T : Over (Spec (CommRingCat.of ℚ)))
    (a : T ⟶ Over.mk actualPicard.toBase) (ha : a ≫ schemePi = 1) : a ^ 19 = 1 := by
  calc
    a ^ 19 = a ≫ (𝟙 (Over.mk actualPicard.toBase)) ^ 19 := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = a ≫ schemePi ≫ schemePiConjugate := by rw [schemePi_comp_schemePiConjugate]
    _ = 1 := by rw [← Category.assoc, ha, MonObj.one_comp]
#print axioms solution
