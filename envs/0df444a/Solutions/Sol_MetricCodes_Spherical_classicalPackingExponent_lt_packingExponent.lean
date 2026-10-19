-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingExponent_lt_packingExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/b7b12f70-1ce2-4fb8-9f19-9dc11d2b9c5a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_classicalPackingExponent_lt_packingExponent_of_maximizer
import Theorems.Thm_MetricCodes_Spherical_exists_classicalPackingObjective_interior_maximizer

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    classicalPackingExponent < packingExponent := by
  obtain ⟨s, hs, hs', hmax⟩ :=
    exists_classicalPackingObjective_interior_maximizer
  exact classicalPackingExponent_lt_packingExponent_of_maximizer
    hs hs' hmax
end MetricCodes.Spherical
