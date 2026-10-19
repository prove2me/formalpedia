-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.radiusPackingObjective_le_hierarchyPackingExponent_of_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/f745dba9-6e96-4899-bd69-1c651124e46b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyPackingObjective_le_hierarchyPackingExponent
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_ambient_stabilizer_interlacing
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_chebyshevGamma_pos

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
    {R : ℝ} (hR : 0 < R)
    (hconvergence :
      Tendsto
        (fun r : ℕ =>
          MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
            (ambient R r) (stabilizer R r))
        atTop (𝓝 (radiusPackingObjective R))) :
    (radiusPackingObjective R : EReal) ≤
      MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent := by
  have hereal :
      Tendsto
        (fun r : ℕ =>
          (MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
            (ambient R r) (stabilizer R r) : EReal))
        atTop (𝓝 (radiusPackingObjective R : EReal)) :=
    EReal.tendsto_coe.mpr hconvergence
  apply le_of_tendsto hereal
  exact Eventually.of_forall fun r =>
    MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective_le_hierarchyPackingExponent
      (ambient_stabilizer_interlacing hR r) (chebyshevGamma_pos hR r)
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
