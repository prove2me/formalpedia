-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_finite_map_data_and_geometry_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T07:20:48.071479+00:00
-- url     : https://prove2.me/submissions/e003b889-7c25-4780-9d7c-8873c85751a4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual whole-curve finite-map data and geometry for the original dyadic curve and zero section.
Named downstream consumer: the original actual Picard representation.
-/
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalFiniteMapDataAndGeometryInputsData20261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13DyadicMixedQuadraticPicardGeometryInputs Order13ActualDyadicMixedFiniteMapData
attribute [local instance] MazurTransfer.Order13ActualDyadicMixedFiniteMapData.originalDyadicFiniteMapPrimeProvider20261019
namespace MazurTransfer.ActualDyadicOriginalFiniteMapCertificateProofBoundary20261019
end MazurTransfer.ActualDyadicOriginalFiniteMapCertificateProofBoundary20261019
theorem solution : (dyadicFiniteMapData.m = 3) ∧ (∀ (n : ℕ) (hn : n ≠ 0), (dyadicPowerFiniteMapData n hn).m = n * 3) ∧ (∀ (m₀ : ℕ), ∃ F : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection, m₀ ≤ F.m) ∧ (IsNoetherianRing BaseRing ∧ IsReduced BaseRing ∧ IsProper (curveToBase BaseRing) ∧
    SmoothOfRelativeDimension 1 (curveToBase BaseRing) ∧
    GeometricallyIntegral (curveToBase BaseRing) ∧
    (∀ m₀, ∃ F : SmoothProperCurve.FiniteMapData (curveToBase BaseRing) zeroSection, m₀ ≤ F.m)) := by
  exact ⟨MazurTransfer.Order13ActualDyadicMixedFiniteMapData.dyadicFiniteMapData_degree, MazurTransfer.Order13ActualDyadicMixedFiniteMapData.dyadicPowerFiniteMapData_degree, MazurTransfer.Order13ActualDyadicMixedFiniteMapData.exists_dyadic_finiteMapData_degree_ge, MazurTransfer.Order13ActualDyadicMixedFiniteMapData.actual_dyadic_picard_geometry_and_finite_map_inputs⟩
#print axioms solution
