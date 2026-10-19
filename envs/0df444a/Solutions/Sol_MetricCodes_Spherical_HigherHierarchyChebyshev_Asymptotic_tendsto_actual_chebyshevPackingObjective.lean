-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.tendsto_actual_chebyshevPackingObjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/32ac22cb-698f-4b55-8cb0-f1eae089d598

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_packingObjective_of_limits

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution
    {R : ℝ} (hR : 0 ≤ R)
    (hG : Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Gamma
        (MetricCodes.Spherical.HigherHierarchyChebyshev.ambient R r)
        (MetricCodes.Spherical.HigherHierarchyChebyshev.stabilizer R r))
      atTop (𝓝 (radiusGamma R)))
    (hP : Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.Phi
        (MetricCodes.Spherical.HigherHierarchyChebyshev.ambient R r)
        (MetricCodes.Spherical.HigherHierarchyChebyshev.stabilizer R r))
      atTop (𝓝 (radiusEntropy R))) :
    Tendsto
      (fun r : ℕ => MetricCodes.Spherical.HigherHierarchy.hierarchyPackingObjective
        (MetricCodes.Spherical.HigherHierarchyChebyshev.ambient R r)
        (MetricCodes.Spherical.HigherHierarchyChebyshev.stabilizer R r))
      atTop (𝓝 (radiusPackingObjective R)) :=
  tendsto_packingObjective_of_limits hR hG hP
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
