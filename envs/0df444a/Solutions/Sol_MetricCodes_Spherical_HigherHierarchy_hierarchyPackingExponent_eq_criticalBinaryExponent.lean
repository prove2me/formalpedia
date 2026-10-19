-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyPackingExponent_eq_criticalBinaryExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/ca6f691d-1713-4244-bc71-727a72f96c6d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyChebyshev_Asymptotic_criticalExponent_le_hierarchyPackingExponent
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyPackingExponent_le_criticalExponent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    hierarchyPackingExponent = (CohnElkies.criticalBinaryExponent : EReal) :=
  le_antisymm hierarchyPackingExponent_le_criticalExponent
    MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic.criticalExponent_le_hierarchyPackingExponent
end MetricCodes.Spherical.HigherHierarchy
