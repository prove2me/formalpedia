-- Prove2me | solution 1 for MazurTransfer.order13_actual_complementary_character_kernel_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T00:09:33.802378+00:00
-- url     : https://prove2.me/submissions/b725459d-18b4-4166-a941-9e728dd9f37c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: pairing against the reflected vector has kernel exactly
the original rational fixed line in the SAME actual norm factor.
Named downstream consumer: the complementary arithmetic-character exact sequence.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelReflectionOriginalRestrictedCompleteEquivalencesAndEmbeddingCertificatesExplicitFiniteExponentContextV220261018
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_order13_actual_cyclotomic_quotient_reflection_lines
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

local instance sourceComplementaryKernelRationalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

open Order13ReflectionParameter Order13ActualNormKernelReflection
open Order13ActualReflectionPairingOrthogonality Order13ActualGeometricNineteenDivisorialPairing
open Order13ReflectionSexticSymmetry Order13ActualReflectionCoefficientCovariance Order13CyclotomicReflectionCoefficients
open Order13ActualNineteenTorsionReflection Order13ActualGeometricNineteenTorsionDiamondComparison
namespace MazurTransfer.ActualComplementaryCharacterKernelProofHelpers20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
theorem pi_complementary_character_kernel (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePi)) (ha : a ≠ 0) :
    LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi (piKernelReflection K r a)) =
      Submodule.span (ZMod 19) {a} := by
  have hb : piKernelReflection K r a ≠ 0 := by
    intro h
    apply ha
    apply (piKernelReflection K r).injective
    exact h.trans (map_zero (piKernelReflection K r)).symm
  rw [(MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines).2 K r _ hb]
  change Submodule.span (ZMod 19) {(piKernelReflection K r).symm (piKernelReflection K r a)} = _
  rw [AddEquiv.symm_apply_apply]

theorem piConjugate_complementary_character_kernel (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePiConjugate)) (ha : a ≠ 0) :
    LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate (piConjugateKernelReflection K r a)) =
      Submodule.span (ZMod 19) {a} := by
  have hb : piConjugateKernelReflection K r a ≠ 0 := by
    intro h
    apply ha
    apply (piConjugateKernelReflection K r).injective
    exact h.trans (map_zero (piConjugateKernelReflection K r)).symm
  rw [(MazurTransfer.order13_actual_cyclotomic_quotient_reflection_lines).1 K r _ hb]
  change Submodule.span (ZMod 19) {piKernelReflection K r ((piKernelReflection K r).symm a)} = _
  rw [AddEquiv.apply_symm_apply]

end MazurTransfer.ActualComplementaryCharacterKernelProofHelpers20261018
theorem solution :
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePi)) (ha : a ≠ 0) ,
    LinearMap.ker (kernelCharacterLinear K schemePiConjugate schemePi (piKernelReflection K r a)) =
      Submodule.span (ZMod 19) {a}) ∧
    (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] (r : ReflectionParameter K)
    (a : Additive (Kernel K schemePiConjugate)) (ha : a ≠ 0) ,
    LinearMap.ker (kernelCharacterLinear K schemePi schemePiConjugate (piConjugateKernelReflection K r a)) =
      Submodule.span (ZMod 19) {a}) := by
  exact ⟨MazurTransfer.ActualComplementaryCharacterKernelProofHelpers20261018.pi_complementary_character_kernel, MazurTransfer.ActualComplementaryCharacterKernelProofHelpers20261018.piConjugate_complementary_character_kernel⟩
#print axioms solution
