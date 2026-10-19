-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyKissingExponent_lt_published
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/fe17b649-475d-4c07-a58e-9639268e0900

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyKissingExponent_lt_exact

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
    hierarchyKissingExponent < (0.39661 : ℝ) :=
  hierarchyKissingExponent_lt_exact.trans (by norm_num)
end MetricCodes.Spherical.HigherHierarchy
