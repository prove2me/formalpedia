-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_rational_affine_fibre_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T04:49:24.281446+00:00
-- url     : https://prove2.me/submissions/9f9a9fe7-c89f-445b-8922-6aab54de8c91

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: genuine base-change isomorphisms for both mixed quadratic
affine charts, and their actual dyadic rational fibres identified with the
SAME existing order-thirteen affine curve charts. Named downstream consumer:
gluing the dyadic integral curve and proving its proper generic comparison.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalRationalChartComparisonAndAffineBaseChangeData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticRationalChartComparison Order13MixedQuadraticAffineBaseChange
namespace MazurTransfer.Order13OriginalDyadicRationalAffineFibreInterface20261019
end MazurTransfer.Order13OriginalDyadicRationalAffineFibreInterface20261019
theorem solution : (ordinaryRationalSchemeIso.inv ≫ ordinaryToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase ℚ) ∧ (reciprocalRationalSchemeIso.inv ≫ reciprocalToBase ℚ =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase ℚ) ∧ (ordinaryDyadicRationalFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase ℚ) ∧ (reciprocalDyadicRationalFibreIso.inv ≫ pullback.fst _ _ =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartToBase ℚ) := by
  exact ⟨ordinaryRationalSchemeIso_inv_toBase,reciprocalRationalSchemeIso_inv_toBase,actual_ordinary_dyadic_rational_fibre,actual_reciprocal_dyadic_rational_fibre⟩
#print axioms solution
