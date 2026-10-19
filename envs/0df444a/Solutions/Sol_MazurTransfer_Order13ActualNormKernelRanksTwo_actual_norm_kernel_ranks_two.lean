-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelRanksTwo.actual_norm_kernel_ranks_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T12:39:28.864253+00:00
-- url     : https://prove2.me/submissions/5616360a-98af-4290-a66a-3aeebe766c30

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: each actual Picard norm kernel has dimension two for
its original F19 module, using equality and the product cardinality 19^4.
Named downstream consumer: actual norm-kernel Galois representations
and their arithmetic Kummer/Selmer conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelRanksTwoOriginalModuleContextData20261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelRanksTwo_actual_norm_kernel_cards_eq
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actual_norm_kernel_cardinalities_product_pow_four
noncomputable section
open MazurTransfer CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardSchemeNineteenNorm
open Order13ActualPicardNormKernelGaloisAction Order13ActualNormKernelProductCardinality
open Order13ActualNormKernelRanksTwo Order13ActualGeometricNineteenTorsionCardinality
attribute [local instance] actualNineteenTorsionProductOriginalGroupProvider20261018
  actualNineteenTorsionProductOriginalCommProvider20261018
  actualNineteenTorsionProductOriginalPiHomProvider20261018
  actualNineteenTorsionProductOriginalConjugateHomProvider20261018
attribute [local instance] originalNormKernelRanksTwoPrimeProvider20261018
  originalNormKernelRanksTwoPiFiniteProvider20261018
  originalNormKernelRanksTwoConjugateFiniteProvider20261018
  originalNormKernelRanksTwoPiKernelFiniteProvider20261018
  originalNormKernelRanksTwoConjugateKernelFiniteProvider20261018
  originalNormKernelRanksTwoPiExponentProvider20261018
  originalNormKernelRanksTwoConjugateExponentProvider20261018
  originalNormKernelRanksTwoPiModuleProvider20261018
  originalNormKernelRanksTwoConjugateModuleProvider20261018

theorem solution (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Module.finrank (ZMod 19) (Additive (Kernel K schemePi)) = 2 ∧
      Module.finrank (ZMod 19) (Additive (Kernel K schemePiConjugate)) = 2 := by
  have hp := Module.natCard_eq_pow_finrank (K := ZMod 19) (V := Additive (Kernel K schemePi))
  have hq := Module.natCard_eq_pow_finrank (K := ZMod 19) (V := Additive (Kernel K schemePiConjugate))
  rw [Nat.card_zmod] at hp hq
  change Nat.card (Kernel K schemePi) = _ at hp
  change Nat.card (Kernel K schemePiConjugate) = _ at hq
  have heq := actual_norm_kernel_cards_eq K
  rw [hp,hq] at heq
  have hr := Nat.pow_right_injective (by decide : 2 ≤ 19) heq
  have hprod := actual_norm_kernel_cardinalities_product_pow_four K
  rw [hp,hq,← pow_add] at hprod
  have hs := Nat.pow_right_injective (by decide : 2 ≤ 19) hprod
  constructor <;> omega

#print axioms solution
