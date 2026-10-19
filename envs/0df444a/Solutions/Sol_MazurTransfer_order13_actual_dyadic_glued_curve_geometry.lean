-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_glued_curve_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T04:19:53.766534+00:00
-- url     : https://prove2.me/submissions/e943ce54-2dc9-44cf-af26-d249ac27d3ed

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual glued mixed quadratic curve is smooth, flat
and locally finitely presented over the dyadic localization. Named
 downstream consumer: its proper smooth model and integral Picard family.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_mixed_affine_chart_geometry
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
namespace MazurTransfer.Order13ActualDyadicGluedCurveGeometryProofHelpers20261019
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
universe u
variable (R : Type u) [CommRing R]

theorem curveToBase_smooth_of_charts (hord : Smooth (ordinaryToBase R))
    (hrec : Smooth (reciprocalToBase R)) : Smooth (curveToBase R) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := @RingHom.Smooth.{u,u})
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (f := curveToBase R) (glueData R).openCover
  intro i
  cases i
  · change Smooth (ordinaryChartMap R ≫ curveToBase R)
    rw [ordinaryChartMap_curveToBase]
    exact hord
  · change Smooth (reciprocalChartMap R ≫ curveToBase R)
    rw [reciprocalChartMap_curveToBase]
    exact hrec

theorem actual_dyadic_glued_curve_geometry :
    Smooth (curveToBase BaseRing) ∧ Flat (curveToBase BaseRing) ∧
      LocallyOfFinitePresentation (curveToBase BaseRing) := by
  letI : Smooth (curveToBase BaseRing) := curveToBase_smooth_of_charts BaseRing
    (MazurTransfer.order13_actual_dyadic_mixed_affine_chart_geometry).1.1 (MazurTransfer.order13_actual_dyadic_mixed_affine_chart_geometry).2.1
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end MazurTransfer.Order13ActualDyadicGluedCurveGeometryProofHelpers20261019
theorem solution : Smooth (curveToBase BaseRing) ∧ Flat (curveToBase BaseRing) ∧ LocallyOfFinitePresentation (curveToBase BaseRing) := by
  exact MazurTransfer.Order13ActualDyadicGluedCurveGeometryProofHelpers20261019.actual_dyadic_glued_curve_geometry
#print axioms solution
