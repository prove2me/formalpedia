-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.tendsto_midpointEndpointDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/db13f6f7-6add-49f7-b996-d3f1499f9477

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_MidpointQuadrature_tendsto_midpointCorrection_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_MidpointQuadrature_midpointEndpointDifference_eq_correction_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Set
open scoped Topology BigOperators
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
namespace MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
theorem _root_.solution
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hg : ContinuousOn g (Set.Icc 0 1))
    (hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (g x) x) :
    Tendsto (midpointEndpointDifference f) atTop
      (𝓝 ((f 0 + f 1) / 2)) := by
  have hsum := (tendsto_midpointCorrection_zero hf hg hderiv).add_const
    ((f 0 + f 1) / 2)
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (midpointEndpointDifference_eq_correction_add f hN).symm
end MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
