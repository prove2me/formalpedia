-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_picard_geometry_and_unique_integral_norm_extensions
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T09:15:43.238034+00:00
-- url     : https://prove2.me/submissions/f8c428c2-b172-488d-8440-0cb705e63e74

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same chosen dyadic Picard geometry and unique integral extensions of every transported rational endomorphism, including both actual norm factors.
Named downstream consumer: original integral norm group laws, scalar nineteen composition, finite etale fibres and inertia at two.
-/
import Definitions.Def_MazurTransfer_Order13DyadicOriginalPicardGeometryAndUniqueNormExtensionsData20261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalChosenPicardNeronModelData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13ActualDyadicMixedPicardNeronModel
open Order13DyadicMixedRationalPicardComparison Order13DyadicMixedPicardGeometry
open Order13DyadicMixedGenericNorms Order13DyadicMixedIntegralNormExtensions
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedPicardNeronModel.originalDyadicChosenPicardNeronPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
attribute [local instance] MazurTransfer.Order13DyadicMixedPicardGeometry.instFactPrimeOfNatNat_order13DyadicMixedPicardGeometry
attribute [local instance] MazurTransfer.Order13DyadicMixedGenericNorms.instFactPrimeOfNatNat_order13DyadicMixedGenericNorms
attribute [local instance] MazurTransfer.Order13DyadicMixedIntegralNormExtensions.instFactPrimeOfNatNat_order13DyadicMixedIntegralNormExtensions
namespace MazurTransfer.ActualDyadicOriginalGeometryNormExtensionProofBoundary20261019
end MazurTransfer.ActualDyadicOriginalGeometryNormExtensionProofBoundary20261019
theorem solution : (Smooth dyadicPicard.toBase ∧ IsProper dyadicPicard.toBase ∧
    GeometricallyConnected dyadicPicard.toBase) ∧ (Smooth rationalPicard.toBase ∧ IsProper rationalPicard.toBase ∧
    GeometricallyConnected rationalPicard.toBase) ∧ (∀ (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase), ∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericNorm φ) ∧ ((∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericPi) ∧
    (∃! ψ : SchemeHomOver dyadicPicard.toBase dyadicPicard.toBase,
      genericFibreRestrict BaseRing ℚ dyadicPicard.toBase dyadicPicard.toBase ψ = genericPiConjugate)) := by
  exact ⟨MazurTransfer.Order13DyadicMixedPicardGeometry.dyadicPicard_geometry, MazurTransfer.Order13DyadicMixedPicardGeometry.rationalPicard_geometry, MazurTransfer.Order13DyadicMixedIntegralNormExtensions.norm_unique_extension, MazurTransfer.Order13DyadicMixedIntegralNormExtensions.actual_norms_have_unique_dyadic_integral_extensions⟩
#print axioms solution
