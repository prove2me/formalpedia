-- Prove2me | solution 1 for MazurTransfer.Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T07:22:45.133973+00:00
-- url     : https://prove2.me/submissions/889dd312-618f-4908-94f3-359939b2086e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original-base degree-zero Picard subfunctor representation
of the literal order-13 curve over a noetherian integral ring with 104
invertible. Smoothness, properness and geometric connectedness are checked.
Named downstream consumer: the compatible integral Jacobian family and
rational/mod-3/mod-5 Picard fibre identification.
Reuses the complete official Anthropic FLT representability theorem at pin
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, without extra inputs.
-/
/- Public proof boundary: original full actual integral Picard representation contract from the original FLT representability theorem, with actual finite-map data and already Proved public geometry/chart-section inputs. No older chosen finite-map record or Picard representative is asserted equal. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FiniteMapDataFromPublicCharts
import Definitions.Def_MazurTransfer_Order13ActualPicardTripleFamily
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_proper
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_smooth_relative_dimension_one
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardChartSections_actual_hasChartSections
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    ∃ D : RelativePic0Designation R (curveToBase R),
      Nonempty (RepresentsRelSubPic (curveToBase R)
        (Order13IntegralSections.positiveInfinitySection R)
        (algEquivZeroCut (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  letI : IsProper (curveToBase R) := MazurTransfer.order13_actual_integral_curve_proper R
  letI : SmoothOfRelativeDimension 1 (curveToBase R) :=
    MazurTransfer.order13_actual_integral_curve_smooth_relative_dimension_one R h104
  letI : GeometricallyIntegral (curveToBase R) :=
    MazurTransfer.order13_actual_integral_curve_geometrically_integral R h104
  exact exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced R
    (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)
    (Order13SingleSectionArbitrarilyLargeFiniteMapData.exists_actual_finiteMapData_degree_ge R h104)
    (Fintype.card (Fin 3 → Fin 6)) 2 5 (by decide)
    (Order13ActualIntegralPicardChartSections.actualTripleFamily R)
    (Order13ActualIntegralPicardChartSections.actual_hasChartSections R h104)
#print axioms solution
