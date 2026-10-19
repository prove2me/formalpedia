-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.eventually_strict_weight_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/fb7cf0f2-24fe-4ae3-a3b8-feb7b43d944f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_shellWeight_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_dimension_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_add_degree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_degree_lt_of_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Rate
open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics
namespace MetricCodes.Johnson.Rate
theorem _root_.solution
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop, 2 * shellWeight a n < n := by
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hww := tendsto_add_degree_ratio hw hw
  have hstrict := eventually_degree_lt_of_ratio hww
    tendsto_dimension_ratio (by linarith [h.weight_lt_half])
  filter_upwards [hstrict] with n hn
  omega
end MetricCodes.Johnson.Rate
