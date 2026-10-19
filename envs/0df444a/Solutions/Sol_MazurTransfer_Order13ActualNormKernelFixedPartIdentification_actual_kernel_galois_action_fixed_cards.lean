-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelFixedPartIdentification.actual_kernel_galois_action_fixed_cards
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T20:11:48.214974+00:00
-- url     : https://prove2.me/submissions/fb649efc-7788-4f4c-8f9b-fdff24de670a

import Mathlib
import Definitions.Def_MazurTransfer_Order13KernelActionFixedSubgroupOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalNormKernelEquivalencesOriginalData20261018
import Theorems.Thm_MazurTransfer_Order13ActualRationalNormKernelOrdering_actual_arithmetic_norm_kernel_cards
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact ordered arithmetic norm-kernel cardinalities transport to the Galois-fixed subgroups of the original geometric norm kernels. Named downstream consumer: actual invariant-space dimensions and cyclotomic quotients.
-/
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardNormKummerCocycles Order13ActualPicardGaloisFixedPointDescent
open Order13ActualNormFixedKernelEquivalence
open Order13ActualPicardRationalNormComparison
open Order13ActualKernelActionFixedSubgroup
open scoped CategoryTheory.MonObj
local instance actualKernelFixedCardsOriginalProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).grpObj
local instance actualKernelFixedCardsOriginalProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard from actualRepresentation).isCommMonObj
local instance actualKernelFixedCardsOriginalProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualKernelFixedCardsOriginalProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (𝒱 : (curveScheme ℚ).TwoAffineOpenCover)

include 𝒱 in
theorem solution :
    Nat.card (kernelGaloisFixed K schemePi) = 1 ∧
      Nat.card (kernelGaloisFixed K schemePiConjugate) = 19 := by
  rw [kernelGaloisFixed_card, kernelGaloisFixed_card,
    fixedNormKernel_card, fixedNormKernel_card]
  change Nat.card rationalPi.ker = 1 ∧ Nat.card rationalPiConjugate.ker = 19
  rw [Nat.card_congr (Order13ActualPicardRationalNormKernelCardinality.rationalPiKernelEquiv 𝒱),
    Nat.card_congr (Order13ActualPicardRationalNormKernelCardinality.rationalPiConjugateKernelEquiv 𝒱)]
  exact Order13ActualRationalNormKernelOrdering.actual_arithmetic_norm_kernel_cards 𝒱
#print axioms solution
