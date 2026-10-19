-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_card_eq_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T10:19:28.775575+00:00
-- url     : https://prove2.me/submissions/0ce936f5-1c9c-473d-8a9b-2a88c83ff129

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric nineteen-torsion on the SAME actual rational
Picard has cardinality 19^4 and F19 dimension four; the dimensions of its
two actual norm kernels sum to four. Individual norm degrees remain separate.
Named downstream consumer: geometric ranks of the actual norm Galois modules.
Uses checked original Anthropic FLT torsion cardinality at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgPointsComparisonData20261018
import Theorems.Thm_MazurTransfer_Order13ActualPicardRationalDimensionTwo_actualPicard_abelian
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actualPicard_fibre_dimension_two
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_torsionBy_algPoints_eq_pow_of_topologicalKrullDim_eq
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardRationalDimensionTwo
open Order13ActualPicardAlgPointsComparison Order13ActualNormKernelProductCardinality
open Order13ActualGeometricNineteenTorsionCardinality
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

theorem solution :
    Nat.card (NineteenTorsion K) = 19 ^ 4 := by
  rw [Nat.card_congr (actualNineteenTorsionAlgPointsEquiv K)]
  exact RelativeGroupLaw.natCard_torsionBy_algPoints_eq_pow_of_topologicalKrullDim_eq
    actualLaw actualLaw_isCommutative actualPicard_abelian 2 actualPicard_fibre_dimension_two
    K 19 (by norm_num : (19 : ℚ) ≠ 0)


#print axioms solution
