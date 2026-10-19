-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingObjective_le_endpointUpper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/e1ebeede-659a-415b-92cb-f939417fe29e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_lower_logb_add_fraction
import Theorems.Thm_MetricCodes_Spherical_classical_geometric_logarithm_cancellation
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_fraction_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    classicalPackingObjective s ≤ classicalEndpointUpper s := by
  have ha := MetricCodes.classicalThreshold_pos hs hs'
  have hentropy := sphericalEntropy_lower_logb_add_fraction ha
  have hcancel := classical_geometric_logarithm_cancellation hs hs'
  have hfraction := classicalThreshold_fraction_eq hs hs'
  unfold classicalPackingObjective classicalEndpointUpper
  rw [← hfraction]
  linarith
end MetricCodes.Spherical
