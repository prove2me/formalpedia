-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.rateSet_nonempty_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/d9a20ed5-14b6-4c89-87e4-eaf1ca40d648

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Rate_exists_zero_fibre_feasible

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
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    (MetricCodes.Johnson.rateSet d).Nonempty := by
  obtain ⟨a, u, hfeasible⟩ := exists_zero_fibre_feasible hd hdhalf
  exact ⟨MetricCodes.Johnson.shellRate a 0 0 u,
    a, 0, 0, u, hfeasible, rfl⟩
end MetricCodes.Johnson.Rate
