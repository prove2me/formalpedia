-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.criticalExponent_le_of_chebyshev_objective_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/6c362646-9660-49f5-960d-06c47ad31334

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_radiusPackingObjective
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_radiusPackingObjective_le_hierarchyPackingExponent_of_convergence

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchyChebyshev
open MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
noncomputable section
open Filter
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution
    (hconvergence :
      ∀ R : ℝ, 0 < R →
        Tendsto
          (fun r : ℕ =>
            MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
              (ambient R r) (stabilizer R r))
          atTop (𝓝 (radiusPackingObjective R))) :
    (CohnElkies.criticalBinaryExponent : EReal) ≤
      MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent := by
  have hereal :
      Tendsto (fun R : ℝ => (radiusPackingObjective R : EReal))
        atTop (𝓝 (CohnElkies.criticalBinaryExponent : EReal)) :=
    EReal.tendsto_coe.mpr tendsto_radiusPackingObjective
  apply le_of_tendsto hereal
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact radiusPackingObjective_le_hierarchyPackingExponent_of_convergence
    hR (hconvergence R hR)
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
