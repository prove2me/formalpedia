-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_radiusPackingObjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/9141ee63-a57e-4aac-bbd8-bafabd2da1b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_inverseQuadratic_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_quadraticCoordinate_inverseQuadratic
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_inverseQuadratic_atTop
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_radiusPackingObjective_quadraticCoordinate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_degreePackingObjective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter
open scoped Topology BigOperators Interval
open MetricCodes.Spherical.HigherHierarchyChebyshev MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution :
    Tendsto radiusPackingObjective atTop
      (𝓝 CohnElkies.criticalBinaryExponent) := by
  have hlimit := tendsto_degreePackingObjective.comp
    tendsto_inverseQuadratic_atTop
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hdegree : 0 < inverseQuadratic R := by
    have hsquare := quadraticCoordinate_inverseQuadratic hR.le
    have hnonneg := inverseQuadratic_nonneg hR.le
    by_contra hnot
    have hzero : inverseQuadratic R = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
    simp [hzero, MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate] at hsquare
    linarith
  have hquadratic := quadraticCoordinate_inverseQuadratic hR.le
  unfold MetricCodes.Spherical.HigherHierarchy.quadraticCoordinate at hquadratic
  change degreePackingObjective (inverseQuadratic R) = radiusPackingObjective R
  symm
  calc
    radiusPackingObjective R =
        radiusPackingObjective
          (inverseQuadratic R * (1 + inverseQuadratic R)) := by rw [hquadratic]
    _ = degreePackingObjective (inverseQuadratic R) :=
      radiusPackingObjective_quadraticCoordinate hdegree
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
