-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingObjective_lt_packingExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/605fc822-7c43-4c97-8180-880494e2d154

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_packingObjective_le_packingExponent
import Theorems.Thm_MetricCodes_Spherical_exists_strict_improving_spherical_feasible

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (classicalPackingObjective s : EReal) < packingExponent := by
  obtain ⟨a, b, hfeasible, himprove⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  calc
    (classicalPackingObjective s : EReal) <
        (packingObjective s a b : EReal) := by
          apply EReal.coe_lt_coe
          unfold classicalPackingObjective packingObjective
          linarith
    _ ≤ packingExponent :=
      packingObjective_le_packingExponent hs hs' hfeasible
end MetricCodes.Spherical
