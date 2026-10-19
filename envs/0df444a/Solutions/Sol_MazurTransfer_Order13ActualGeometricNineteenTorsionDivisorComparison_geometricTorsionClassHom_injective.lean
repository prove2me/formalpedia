-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionDivisorComparison.geometricTorsionClassHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T11:01:40.598694+00:00
-- url     : https://prove2.me/submissions/22b6b911-ccd5-41dd-a905-e82fbfd02c14

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: injectivity of the original natural divisor-class map
on the SAME actual Picard nineteen-torsion.
Named downstream consumer: the natural geometric nineteen-torsion
additive equivalence and transport of the actual Weil pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualGeometricNineteenTorsionNaturalDivisorMapOriginalFieldContextDataV320261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticGroup_geometricArithmeticClassOver_injective_explicitOriginalType20261017
noncomputable section
open MazurTransfer
open Order13ActualGeometricNineteenTorsionDivisorComparison
attribute [local instance] naturalDivisorMapOriginalFactProvider20261018 naturalDivisorMapOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Function.Injective (geometricTorsionClassHom K) := by
  intro x y hxy
  apply Subtype.ext
  exact Order13ActualPicardGeometricArithmeticGroup.geometricArithmeticClassOver_injective_explicitOriginalType20261017
    K (GoodCharacteristicGeometryPublicProof.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K)
    (congrArg Subtype.val hxy)

#print axioms solution
