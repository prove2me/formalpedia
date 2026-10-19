-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyKissingExponent_lt_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/d627e1c5-f165-4750-b9a7-57c8cca31807

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_kissing_entropy_certificate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Numerics_kissing_entropy_certificate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_kissing_levelTwo_feasible

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    hierarchyKissingExponent < (0.396605 : ℝ) := by
  unfold hierarchyKissingExponent
  exact lt_of_le_of_lt
    (hierarchyVariationalRate_le_of_feasible
      kissing_levelTwo_feasible.1 kissing_levelTwo_feasible.2)
    Numerics.kissing_entropy_certificate
end MetricCodes.Spherical.HigherHierarchy
