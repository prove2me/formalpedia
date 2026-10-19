-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelProductCardinality.nineteenTorsion_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T08:47:33.700841+00:00
-- url     : https://prove2.me/submissions/19942c71-a758-4625-bea7-7d71f28e1942

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: nineteen-torsion of the SAME actual Picard scheme splits
as the product of its two actual norm kernels over any characteristic-zero field.
Named downstream consumer: deriving geometric norm kernel dimensions from
actual Picard torsion cardinality. No numerical dimension or degree is asserted. -/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
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


theorem solution : Finite (NineteenTorsion K) := by
  letI : IsFinite schemePi.left := (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1
  letI : IsFinite schemePiConjugate.left := (Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).2.1
  letI : Finite (Kernel K schemePi) := kernel_finite K schemePi
  letI : Finite (Kernel K schemePiConjugate) := kernel_finite K schemePiConjugate
  exact Finite.of_equiv _ (kernelProductEquiv K).symm

#print axioms solution
