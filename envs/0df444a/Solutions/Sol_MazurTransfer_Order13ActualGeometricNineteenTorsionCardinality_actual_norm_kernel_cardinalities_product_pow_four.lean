-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_norm_kernel_cardinalities_product_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T10:44:39.143592+00:00
-- url     : https://prove2.me/submissions/af0ef9e8-158e-44d9-932a-d0795e3adf76

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: nineteen-torsion of the SAME actual Picard scheme splits
as the product of its two actual norm kernels over any characteristic-zero field.
Named downstream consumer: deriving geometric norm kernel dimensions from
actual Picard torsion cardinality. No numerical dimension or degree is asserted. -/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelProductCardinality_nineteenTorsion_card_eq_kernel_product
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actual_nineteenTorsion_card_eq_pow_four
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
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelFiniteModule


open Order13ActualGeometricNineteenTorsionCardinality

theorem solution :
    Nat.card (Kernel K schemePi) * Nat.card (Kernel K schemePiConjugate) = 19 ^ 4 := by
  rw [← nineteenTorsion_card_eq_kernel_product K]
  exact actual_nineteenTorsion_card_eq_pow_four K

#print axioms solution
