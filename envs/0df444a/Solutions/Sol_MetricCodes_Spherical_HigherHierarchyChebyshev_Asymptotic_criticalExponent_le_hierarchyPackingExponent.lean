-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.criticalExponent_le_hierarchyPackingExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/99c4b2f4-bcb7-47f8-9e6c-f0a10a89f203

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_Phi_chebyshev
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_Gamma_chebyshev
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_tendsto_actual_chebyshevPackingObjective
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_criticalExponent_le_of_chebyshev_objective_convergence

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchyChebyshev
open MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
noncomputable section
namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
theorem _root_.solution :
    (CohnElkies.criticalBinaryExponent : EReal) ≤
      MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent := by
  apply criticalExponent_le_of_chebyshev_objective_convergence
  intro R hR
  exact tendsto_actual_chebyshevPackingObjective hR.le
    (tendsto_Gamma_chebyshev hR) (tendsto_Phi_chebyshev hR)
end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic
