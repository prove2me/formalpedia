-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicExactSequence.actual_cyclotomic_exact_sequence_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T20:53:40.927623+00:00
-- url     : https://prove2.me/submissions/b68d67b3-0fa1-4547-a200-4a2f39664070

import Definitions.Def_MazurTransfer_Order13CyclotomicKernelExactSequenceOriginalDataAndStructuralCertificates20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicQuotient_actual_cyclotomic_quotient_dichotomy
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicExactSequence_hasCyclotomicExactSequence_of_quotient
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm factor opposite the actual invariant line
has an equivariant quotient onto the literal cyclotomic19 representation,
with a one-dimensional kernel. Both possible factor orderings are retained.
Named downstream consumer: identifying the remaining arithmetic13 character
and proving the actual local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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

open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualNormKernelRanksTwo
open Order13ActualPicardSchemeNineteenNorm
attribute [local instance] originalNormKernelRanksTwoPiFiniteProvider20261018 originalNormKernelRanksTwoConjugateFiniteProvider20261018 originalNormKernelRanksTwoPiExponentProvider20261018 originalNormKernelRanksTwoConjugateExponentProvider20261018 originalNormKernelRanksTwoPiModuleProvider20261018 originalNormKernelRanksTwoConjugateModuleProvider20261018

local instance sourceActualCyclotomicExactSequenceFact104Provider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ActualNormKernelCyclotomicExactSequence

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      HasCyclotomicExactSequence K schemePiConjugate ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 ∧
      HasCyclotomicExactSequence K schemePi ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0) := by
  rcases actual_cyclotomic_quotient_dichotomy K 𝒱 with ⟨hp, hq, hb⟩ | ⟨hb, hq, hp⟩
  · exact Or.inl ⟨hp, hasCyclotomicExactSequence_of_quotient K schemePiConjugate hq, hb⟩
  · exact Or.inr ⟨hb, hasCyclotomicExactSequence_of_quotient K schemePi hq, hp⟩
#print axioms solution
