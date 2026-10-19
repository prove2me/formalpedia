-- Prove2me | solution 1 for MetricCodes.Spherical.kissing_witness_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/acf540e7-a6db-4d33-b9db-efb3db574757

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_kissing_witness_domain
import Theorems.Thm_MetricCodes_Numerics_kissing_spectral_certificate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution :
    Feasible ((1 : ℝ) / 2)
      MetricCodes.Numerics.kissingA MetricCodes.Numerics.kissingB := by
  exact ⟨MetricCodes.Numerics.kissing_witness_domain.1,
    MetricCodes.Numerics.kissing_witness_domain.2,
    MetricCodes.Numerics.kissing_spectral_certificate⟩
end MetricCodes.Spherical
