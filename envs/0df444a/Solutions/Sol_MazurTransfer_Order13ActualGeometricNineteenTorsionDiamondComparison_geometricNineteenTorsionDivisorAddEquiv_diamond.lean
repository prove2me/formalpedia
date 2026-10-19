-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionDiamondComparison.geometricNineteenTorsionDivisorAddEquiv_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T11:54:20.721149+00:00
-- url     : https://prove2.me/submissions/ab2270bc-2f82-4def-bbd6-308bf0c10ba0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME natural nineteen-torsion divisor-class
equivalence intertwines the original actual Picard diamond with the
original arithmetic field diamond.
Named downstream consumer: invariance of the transported actual Weil
pairing under diamond and adjointness of the two actual norm factors.
-/
import Definitions.Def_MazurTransfer_Order13ActualNineteenTorsionDiamondOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_actualGenericDiamondHom
noncomputable section
open CategoryTheory
open MazurTransfer AlgebraicCurve
open Order13ActualNormKernelProductCardinality Order13ActualGeometricNineteenTorsionDivisorComparison
open Order13ActualGeometricNineteenTorsionDiamondComparison
open Order13ActualPicardGeometricArithmeticClass Order13ActualPicardGeometricArithmeticGroup
open Order13ActualPicardGeometricDiamondGroupAction Order13ActualPicardGenericFieldAction
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018
attribute [local instance] nineteenTorsionDiamondOriginalFactProvider20261018 nineteenTorsionDiamondOriginalAlgebraProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (x : NineteenTorsion K) :
    geometricNineteenTorsionDivisorAddEquiv K (actualNineteenTorsionDiamondHom K x) =
      arithmeticNineteenTorsionDiamondHom K (geometricNineteenTorsionDivisorAddEquiv K x) := by
  apply Subtype.ext
  change geometricArithmeticClassOver K _ (x.val.toMul ≫ schemeDiamond) =
    Order13FieldDiamondPicardEndomorphisms.rho K (geometricArithmeticClassOver K _ x.val.toMul)
  exact geometricArithmeticClass_actualGenericDiamondHom K _ (pointOfOverHom K x.val.toMul)

#print axioms solution
