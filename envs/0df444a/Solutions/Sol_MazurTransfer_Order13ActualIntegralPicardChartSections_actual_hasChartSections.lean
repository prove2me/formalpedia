-- Prove2me | solution 1 for MazurTransfer.Order13ActualIntegralPicardChartSections.actual_hasChartSections
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:47:55.139019+00:00
-- url     : https://prove2.me/submissions/5f99a8bf-d3ca-4855-a59d-5538310dcb97

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: all 216 ordered triples of the six actual marked sections
satisfy the original integral Picard chart-section contract with g=2, r=5.
Named downstream consumer: original-base representation of the degree-zero
Picard subfunctor for the literal order-13 curve.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardTripleFamily
import Theorems.Thm_MazurTransfer_SixSectionPicardChartCriterion_hasChartSections_of_six_sections
import Theorems.Thm_MazurTransfer_Order13SixMarkedSectionsDistinct_six_sections_field_precomposition_injective
import Theorems.Thm_MazurTransfer_Order13GeometricFibreGenusTwoModels_geometric_fibre_genus_two_models
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections MazurTransfer.SixSectionPicardChartCriterion
open MazurTransfer.Order13ActualIntegralPicardChartSections
open MazurTransfer
theorem solution (R : Type u) [CommRing R]  (h104 : IsUnit (104 : R)) :
    HasChartSections (curveToBase R) (g := 2) (r := 5) (actualTripleFamily R) := by
  have h2 : IsUnit (2 : R) := by
    have hh : IsUnit ((2 : R)*52) := by convert h104 using 1; ring
    exact (IsUnit.mul_iff.mp hh).1
  exact hasChartSections_of_six_sections (curveToBase R) (sixMarkedSections R)
    (fun k _ _ s => Order13SixMarkedSectionsDistinct.six_sections_field_precomposition_injective R h2 k s)
    (fun k _ _ s => Order13GeometricFibreGenusTwoModels.geometric_fibre_genus_two_models R h104 k s)
#print axioms solution
