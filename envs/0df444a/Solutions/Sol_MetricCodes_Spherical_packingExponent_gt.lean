-- Prove2me | solution 1 for MetricCodes.Spherical.packingExponent_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/ed213f4c-2018-4c07-8272-82e1139925fc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_packing_witness_domain
import Theorems.Thm_MetricCodes_Numerics_packing_entropy_certificate
import Theorems.Thm_MetricCodes_Spherical_packingObjective_le_packingExponent
import Theorems.Thm_MetricCodes_Spherical_packing_witness_feasible

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution :
    ((0.602872829455 : ℝ) : EReal) < packingExponent := by
  calc
    ((0.602872829455 : ℝ) : EReal) <
        (packingObjective MetricCodes.Numerics.packingS
          MetricCodes.Numerics.packingA MetricCodes.Numerics.packingB : EReal) := by
            apply EReal.coe_lt_coe
            exact MetricCodes.Numerics.packing_entropy_certificate
    _ ≤ packingExponent :=
      packingObjective_le_packingExponent
        MetricCodes.Numerics.packing_witness_domain.1
        MetricCodes.Numerics.packing_witness_domain.2.1
        packing_witness_feasible
end MetricCodes.Spherical
