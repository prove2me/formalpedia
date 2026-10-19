-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.hasCyclotomicExactSequence_of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T20:45:47.085992+00:00
-- url     : https://prove2.me/submissions/83277928-39c2-4039-9f5e-a297ba46d80d

import Definitions.Def_MazurTransfer_Order13CyclotomicKernelExactSequenceOriginalDataAndStructuralCertificates20261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original equivariant cyclotomic quotient gives the original short exact sequence. Named downstream consumer: Order13ActualNormKernelCyclotomicExactSequence.actual_cyclotomic_exact_sequence_dichotomy.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve MazurTransfer
open NeronModelInfra GoodReductionJacobian
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelCyclotomicQuotient
open Order13ActualNormKernelF19Representation NineteenRootsGaloisRepresentation
open Order13ActualNineteenTorsionNormPairingAdjoint Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelNineteenEmbedding
open scoped CategoryTheory.MonObj
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018 kernelNineteenEmbeddingOriginalFiniteProvider20261018

open Order13ActualNormKernelCyclotomicExactSequence

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom ψ] [IsFinite ψ.left] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (h : HasCyclotomicQuotient K ψ) : HasCyclotomicExactSequence K ψ := by
  rcases h with ⟨f, hs, hd⟩
  exact ⟨f, hs, cyclotomicKernelInclusion_injective K ψ f,
    cyclotomicKernelInclusion_range K ψ f, hd⟩
#print axioms solution
