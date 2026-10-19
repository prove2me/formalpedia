-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelProductCardinality.nineteenTorsion_card_eq_kernel_product
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T08:42:58.500603+00:00
-- url     : https://prove2.me/submissions/7f230e38-18d1-44ff-a4cd-7e9456d6979b

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: nineteen-torsion of the SAME actual Picard scheme splits
as the product of its two actual norm kernels over any characteristic-zero field.
Named downstream consumer: deriving geometric norm kernel dimensions from
actual Picard torsion cardinality. No numerical dimension or degree is asserted. -/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
noncomputable section
open MazurTransfer
open Order13ActualNormKernelProductCardinality
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018 actualNineteenTorsionProductOriginalCommProvider20261018 actualNineteenTorsionProductOriginalPiHomProvider20261018 actualNineteenTorsionProductOriginalConjugateHomProvider20261018


open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K]

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelFiniteModule


theorem solution :
    Nat.card (NineteenTorsion K) = Nat.card (Kernel K schemePi) * Nat.card (Kernel K schemePiConjugate) := by
  rw [Nat.card_congr (kernelProductEquiv K), Nat.card_prod]


#print axioms solution
