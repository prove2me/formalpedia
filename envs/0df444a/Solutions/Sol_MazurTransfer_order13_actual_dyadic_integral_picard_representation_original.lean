-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_integral_picard_representation_original
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T07:54:01.809286+00:00
-- url     : https://prove2.me/submissions/d1ad9be5-8c67-4930-b8bd-a069db26d41f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: degree-zero Picard representation of the SAME actual mixed
curve and fixed zeroSection over Z_(2), smooth, proper and geometrically connected.
Named downstream consumer: identifying its rational Picard fibre and extending
both norm factors for the order-13 dyadic good-reduction argument.
Uses the complete official Anthropic FLT representability theorem at exact
pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFiniteMapDataAndGeometryInputsData20261019
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalCurveModelsGenusTwoAndPicardChartSectionsData20261019
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard MazurTransfer
open GoodReductionJacobian
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs
open Order13ActualDyadicMixedFiniteMapData Order13ActualDyadicMixedPicardChartSections
attribute [local instance] MazurTransfer.Order13DyadicMixedQuadraticPicardGeometryInputs.originalDyadicPicardZeroSectionPrimeProvider20261019
namespace MazurTransfer.Order13ActualDyadicMixedPicardRepresentation
theorem actual_dyadic_integral_picard_representation :
    ∃ D : RelativePic0Designation BaseRing (curveToBase BaseRing),
      Nonempty (RepresentsRelSubPic (curveToBase BaseRing) zeroSection
        (algEquivZeroCut (curveToBase BaseRing) zeroSection) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  obtain ⟨hN,hR,hP,hD,hG,-⟩ := actual_dyadic_picard_geometry_and_finite_map_inputs
  letI : IsNoetherianRing BaseRing := hN
  letI : IsReduced BaseRing := hR
  letI : IsProper (curveToBase BaseRing) := hP
  letI : SmoothOfRelativeDimension 1 (curveToBase BaseRing) := hD
  letI : GeometricallyIntegral (curveToBase BaseRing) := hG
  exact exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced BaseRing
    (curveToBase BaseRing) zeroSection exists_dyadic_finiteMapData_degree_ge
    (Fintype.card (Fin 3 → Fin 6)) 2 5 (by decide)
    actualTripleFamily actual_hasChartSections

end MazurTransfer.Order13ActualDyadicMixedPicardRepresentation
theorem solution : ∃ D : RelativePic0Designation BaseRing (curveToBase BaseRing),
      Nonempty (RepresentsRelSubPic (curveToBase BaseRing) zeroSection
        (algEquivZeroCut (curveToBase BaseRing) zeroSection) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  exact MazurTransfer.Order13ActualDyadicMixedPicardRepresentation.actual_dyadic_integral_picard_representation
#print axioms solution
