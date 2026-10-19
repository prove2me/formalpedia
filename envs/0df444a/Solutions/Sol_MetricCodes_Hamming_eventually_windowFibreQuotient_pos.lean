-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_windowFibreQuotient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/365e082b-f363-496d-8344-c50e410cf930

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_windowFibreQuotient_pos_of_fit

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < windowFibreQuotient a b n := by
  filter_upwards [eventually_transverse_add_le_longitudinal hb hba 0]
    with n hfit
  apply windowFibreQuotient_pos_of_fit ha
  omega
end MetricCodes.Hamming
