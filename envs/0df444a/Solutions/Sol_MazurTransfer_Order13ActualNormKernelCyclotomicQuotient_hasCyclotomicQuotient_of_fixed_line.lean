-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelCyclotomicQuotient.hasCyclotomicQuotient_of_fixed_line
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T16:23:51.760262+00:00
-- url     : https://prove2.me/submissions/3c21df69-c717-4cf7-bfc9-52237c6cc2a0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual norm factor opposite the actual invariant line
has an equivariant quotient onto the literal cyclotomic19 representation,
with a one-dimensional kernel. Both possible factor orderings are retained.
Named downstream consumer: identifying the remaining arithmetic13 character
and proving the actual local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelCyclotomicQuotientOriginalPredicateData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelCyclotomicCharacter_kernelCharacterLinear_surjective_of_cross
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

theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K]
    (φ ψ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    [IsMonHom φ] [IsMonHom ψ] [IsFinite φ.left] [IsFinite ψ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] [Fact (∀ z : Kernel K ψ, z ^ 19 = 1)]
    (hcross : ∀ x : (actualNineteenTorsionNormHom K φ).ker,
      (∀ y : (actualNineteenTorsionNormHom K ψ).ker,
        Order13ActualGeometricNineteenDivisorialPairing.actualGeometricNineteenPairing K x.val y.val = 1) → x = 0)
    (hI : Module.finrank (ZMod 19) (kernelRepresentation K φ).invariants = 1)
    (hV : Module.finrank (ZMod 19) (Additive (Kernel K ψ)) = 2) :
    HasCyclotomicQuotient K ψ := by
  have hp : 0 < Module.finrank (ZMod 19) (kernelRepresentation K φ).invariants := by
    rw [hI]
    decide
  obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  have ha0 : a.val ≠ 0 := by
    intro hz
    exact ha (Subtype.ext hz)
  let f := kernelCharacterIntertwining K φ ψ a.val (fun σ => a.property σ)
  have hs : Function.Surjective f := kernelCharacterLinear_surjective_of_cross K φ ψ hcross a.val ha0
  refine ⟨f, hs, ?_⟩
  have hd := LinearMap.finrank_range_add_finrank_ker f.toLinearMap
  rw [LinearMap.range_eq_top.mpr hs, _root_.finrank_top, roots_finrank_one K, hV] at hd
  omega
#print axioms solution
