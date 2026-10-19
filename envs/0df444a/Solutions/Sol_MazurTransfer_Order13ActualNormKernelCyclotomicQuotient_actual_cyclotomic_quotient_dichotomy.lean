-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.actual_cyclotomic_quotient_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T20:31:47.817621+00:00
-- url     : https://prove2.me/submissions/4984c9c1-422f-47b7-9f69-2a9dcaff7880

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicQuotient_hasCyclotomicQuotient_of_fixed_line
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelRanksTwo_actual_norm_kernel_ranks_two
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCrossPairing_piConjugate_cross_left_nondegenerate
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelInvariantDimensions_actual_kernel_invariant_finranks
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

local instance sourceActualCyclotomicQuotientFact104Provider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 1 ∧
      HasCyclotomicQuotient K schemePiConjugate ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 0) ∨
    (Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 ∧
      HasCyclotomicQuotient K schemePi ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0) := by
  have hi := Order13ActualNormKernelInvariantDimensions.actual_kernel_invariant_finranks K 𝒱
  have hr := Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two K
  exact Or.inr ⟨hi.2, hasCyclotomicQuotient_of_fixed_line K schemePiConjugate schemePi
    (Order13ActualNormKernelCrossPairing.piConjugate_cross_left_nondegenerate K) hi.2 hr.1, hi.1⟩
#print axioms solution
