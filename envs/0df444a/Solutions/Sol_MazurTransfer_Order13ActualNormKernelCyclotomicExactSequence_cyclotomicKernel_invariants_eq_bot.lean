-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.cyclotomicKernel_invariants_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T21:00:58.522688+00:00
-- url     : https://prove2.me/submissions/9ac6c4bc-576a-464e-bc25-6bfcf1f18d25

import Definitions.Def_MazurTransfer_Order13CyclotomicKernelExactSequenceOriginalDataAndStructuralCertificates20261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel representation has no invariants when its ambient actual norm-kernel representation has none. Named downstream consumer: Order13ActualArithmeticCharacterExactSequence.actual_arithmetic_character_exact_sequence_dichotomy.
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
    (f : Representation.IntertwiningMap (kernelRepresentation K ψ) (rootsRepresentation K))
    (hV : (kernelRepresentation K ψ).invariants = ⊥) :
    (cyclotomicKernelRepresentation K ψ f).invariants = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hfixed : v.val ∈ (kernelRepresentation K ψ).invariants := by
    intro σ
    exact congrArg Subtype.val (hv σ)
  rw [hV] at hfixed
  apply Subtype.ext
  exact hfixed
#print axioms solution
