-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicCharacter.kernelCharacter_surjective_of_cross
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T15:39:21.584672+00:00
-- url     : https://prove2.me/submissions/761c2998-8840-48e9-98ad-8fd2a12c6b8c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against an actual fixed norm-kernel vector gives
an equivariant character of the other actual norm kernel into literal roots
of unity. Named downstream consumer: the actual cyclotomic quotient dichotomy.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicCharacterOriginalData20261018
import Theorems.Thm_MazurTransfer_prime_roots_character_surjective
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open Order13ActualNormKernelProductCardinality Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualPicardNormKummerCocycles
open Order13ActualNineteenTorsionGaloisPairingBridge Order13ActualGeometricNineteenDivisorialPairing
open Order13ActualNormKernelCyclotomicCharacter
open NineteenRootsGaloisRepresentation
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (hcross : ∀ x : (actualNineteenTorsionNormHom K φ).ker,
      (∀ y : (actualNineteenTorsionNormHom K ψ).ker,
        actualGeometricNineteenPairing K x.val y.val = 1) → x = 0)
    (a : Additive (Kernel K φ)) (ha : a ≠ 0) :
    Function.Surjective (kernelCharacter K φ ψ a) := by
  apply MazurTransfer.prime_roots_character_surjective K (Kernel K ψ) 19
  by_contra h
  push Not at h
  have hx : kernelRestrictedAddEquiv K φ a = 0 := by
    apply hcross
    intro y
    obtain ⟨z, hz⟩ := kernelRestrictedAddHom_surjective K ψ y
    have hv := congrArg Subtype.val (h z.toMul)
    change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ a)
      (kernelNineteenAddHom K ψ z) = 1 at hv
    rw [← hz]
    exact hv
  apply ha
  apply (kernelRestrictedAddEquiv K φ).injective
  exact hx.trans (map_zero (kernelRestrictedAddEquiv K φ)).symm

#print axioms solution
