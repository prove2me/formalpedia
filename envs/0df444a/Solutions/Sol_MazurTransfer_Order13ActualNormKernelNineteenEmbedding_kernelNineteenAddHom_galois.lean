-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelNineteenEmbedding.kernelNineteenAddHom_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T15:10:31.201713+00:00
-- url     : https://prove2.me/submissions/fe50a43c-09e8-4a90-afc0-cc1af89262b2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complete actual nineteen-killed norm kernel embeds
additively and Galois-equivariantly into the SAME Picard nineteen torsion.
Named downstream consumer: actual cyclotomic quotient maps via the pairing.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelNineteenEmbeddingOriginalData20261018
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelNineteenEmbedding Order13ActualNineteenTorsionGaloisPairingBridge
open scoped CategoryTheory.MonObj
attribute [local instance] kernelNineteenEmbeddingOriginalGroupProvider20261018 kernelNineteenEmbeddingOriginalCommProvider20261018 kernelNineteenEmbeddingOriginalPiHomProvider20261018 kernelNineteenEmbeddingOriginalConjugateHomProvider20261018 kernelNineteenEmbeddingOriginalActionProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018 kernelNineteenEmbeddingOriginalModuleProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [IsAlgClosed K] (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K φ)) :
    arithmeticNineteenTorsionHom K σ (kernelNineteenAddHom K φ z) =
      kernelNineteenAddHom K φ (Order13ActualNormKernelF19Representation.kernelRepresentation K φ σ z) := by
  apply Subtype.ext
  rfl

#print axioms solution
