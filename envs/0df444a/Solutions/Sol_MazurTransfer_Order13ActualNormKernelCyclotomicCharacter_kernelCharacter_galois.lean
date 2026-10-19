-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T15:34:08.20216+00:00
-- url     : https://prove2.me/submissions/50c35ce9-4079-49a5-8bb9-5300a18a7d92

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against an actual fixed norm-kernel vector gives
an equivariant character of the other actual norm kernel into literal roots
of unity. Named downstream consumer: the actual cyclotomic quotient dichotomy.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelNineteenEmbedding_kernelNineteenAddHom_galois
import Theorems.Thm_MazurTransfer_Order13ActualNineteenPairingGaloisCovariance_actualPairing_galois
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open Order13ActualNineteenTorsionGaloisPairingBridge Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualNineteenPairingGaloisCovariance Order13ActualNormKernelCyclotomicCharacter
open NineteenRootsGaloisRepresentation
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)] (a : Additive (Kernel K φ))
    (ha : ∀ σ : K ≃ₐ[ℚ] K, kernelRepresentation K φ σ a = a)
    (σ : K ≃ₐ[ℚ] K) (z : Additive (Kernel K ψ)) :
    kernelCharacterLinear K φ ψ a (kernelRepresentation K ψ σ z) =
      rootsRepresentation K σ (kernelCharacterLinear K φ ψ a z) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ a)
    (kernelNineteenAddHom K ψ (kernelRepresentation K ψ σ z)) = _
  rw [← kernelNineteenAddHom_galois]
  have hfixed : arithmeticNineteenTorsionHom K σ (kernelNineteenAddHom K φ a) =
      kernelNineteenAddHom K φ a := (kernelNineteenAddHom_galois K φ σ a).trans
        (congrArg (kernelNineteenAddHom K φ) (ha σ))
  rw [← hfixed]
  exact actualPairing_galois K σ _ _

#print axioms solution
