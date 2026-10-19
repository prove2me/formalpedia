-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardRationalDimensionTwo.actualPicard_abelian
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T08:53:30.247823+00:00
-- url     : https://prove2.me/submissions/d0bcc277-b5f0-4470-a56a-e91e363e72b0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: relative dimension two for the SAME rational Picard
scheme, deduced from its checked geometric base change and connectedness.
Named downstream consumer: actual nineteen-torsion cardinality over
algebraically closed extensions of the rational base.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelProductCardinalityData20261018
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardRepresentation_actual_integral_picard_representation
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism

theorem solution : AbelianSchemePropertyBundle ℚ actualPicard.toBase := by
  have h := (Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation ℚ
    (isUnit_iff_ne_zero.mpr (by norm_num : (104 : ℚ) ≠ 0))).choose_spec
  letI : GeometricallyConnected actualPicard.toBase := h.2.2.2
  exact ⟨h.2.1, h.2.2.1, fun s => actualPicard.toBase.isConnected_preimage_singleton s,
    ⟨actualLaw⟩⟩


#print axioms solution
