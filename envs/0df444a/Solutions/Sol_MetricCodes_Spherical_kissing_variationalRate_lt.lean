-- Prove2me | solution 1 for MetricCodes.Spherical.kissing_variationalRate_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/2f4d3a42-f726-4e40-819d-df1b5e0f0a38

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Johnson_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Numerics_kissing_entropy_certificate
import Theorems.Thm_MetricCodes_Spherical_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_kissing_witness_feasible

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution :
    variationalRate ((1 : ℝ) / 2) < (0.397305601680 : ℝ) := by
  exact lt_of_le_of_lt
    (variationalRate_le_of_feasible kissing_witness_feasible)
    MetricCodes.Numerics.kissing_entropy_certificate
end MetricCodes.Spherical
