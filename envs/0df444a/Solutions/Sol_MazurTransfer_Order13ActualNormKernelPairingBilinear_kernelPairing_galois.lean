-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelPairingBilinear.kernelPairing_galois
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T00:17:23.937426+00:00
-- url     : https://prove2.me/submissions/420d5bd2-ca75-4ebf-806a-8da4f1120f32

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME actual geometric nineteen-pairing on COMPLETE
norm kernels is F19-bilinear and covariant for their EXISTING arithmetic
Galois representations. Named downstream consumer: the complementary
character quotient and its actual intertwiner.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualNormKernelBilinearPairingOriginalDataAndActionCertificateExplicitKernelNamespaceV220261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelNineteenEmbedding_kernelNineteenAddHom_galois
import Theorems.Thm_MazurTransfer_Order13ActualNineteenPairingGaloisCovariance_actualPairing_galois
noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualNormKernelPairingBilinear
open MazurTransfer.Order13ActualNineteenPairingGaloisCovariance
namespace MazurTransfer.ActualBilinearPairingGaloisProofHelpers20261018
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
  [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
theorem kernelPairing_galois (σ : K ≃ₐ[ℚ] K) (a : Additive (Kernel K φ))
    (z : Additive (Kernel K ψ)) :
    kernelPairingLinear K φ ψ (kernelRepresentation K φ σ a) (kernelRepresentation K ψ σ z) =
      rootsRepresentation K σ (kernelPairingLinear K φ ψ a z) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change actualGeometricNineteenPairing K (kernelNineteenAddHom K φ (kernelRepresentation K φ σ a))
    (kernelNineteenAddHom K ψ (kernelRepresentation K ψ σ z)) = _
  rw [← kernelNineteenAddHom_galois, ← kernelNineteenAddHom_galois]
  exact actualPairing_galois K σ _ _

end MazurTransfer.ActualBilinearPairingGaloisProofHelpers20261018
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
open Order13ActualPicardNormKernelGaloisAction
open Order13ActualNormKernelCyclotomicCharacter Order13ActualNormKernelFiniteModule
open Order13ActualNormKernelNineteenEmbedding Order13ActualNormKernelF19Representation
open NineteenRootsGaloisRepresentation Order13ActualNineteenTorsionNormPairingAdjoint
open Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] kernelCharacterOriginalGroupProvider20261018 kernelCharacterOriginalCommProvider20261018 kernelCharacterOriginalPiHomProvider20261018 kernelCharacterOriginalConjugateHomProvider20261018 kernelCharacterOriginalPrimeProvider20261018 kernelCharacterOriginalLeftModuleProvider20261018 kernelCharacterOriginalRightModuleProvider20261018 kernelCharacterOriginalRootsModuleProvider20261018
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
variable (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
  [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
  [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
theorem solution (σ : K ≃ₐ[ℚ] K) (a : Additive (Kernel K φ))
    (z : Additive (Kernel K ψ)) :
    kernelPairingLinear K φ ψ (kernelRepresentation K φ σ a) (kernelRepresentation K ψ σ z) =
      rootsRepresentation K σ (kernelPairingLinear K φ ψ a z) := by
  exact MazurTransfer.ActualBilinearPairingGaloisProofHelpers20261018.kernelPairing_galois K φ ψ σ a z
#print axioms solution
