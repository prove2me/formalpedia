-- Prove2me | solution 1 for MetricCodes.Spherical.packing_witness_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/e92e7f23-45ce-4ac8-a56f-45c5413ee3b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_packing_witness_domain
import Theorems.Thm_MetricCodes_Numerics_packing_spectral_certificate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution :
    Feasible MetricCodes.Numerics.packingS
      MetricCodes.Numerics.packingA MetricCodes.Numerics.packingB := by
  exact ⟨MetricCodes.Numerics.packing_witness_domain.2.2.1,
    MetricCodes.Numerics.packing_witness_domain.2.2.2,
    MetricCodes.Numerics.packing_spectral_certificate⟩
end MetricCodes.Spherical
