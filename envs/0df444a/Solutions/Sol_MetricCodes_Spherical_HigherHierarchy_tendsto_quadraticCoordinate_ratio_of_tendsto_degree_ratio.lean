-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_quadraticCoordinate_ratio_of_tendsto_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/adf4e756-1b38-4d10-9705-f6ecd49dde71

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_shifted_degree_ratio_of_tendsto_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => v n / u n) atTop (nhds d)) :
    Tendsto (fun n => quadraticCoordinate (v n) /
      quadraticCoordinate (u n)) atTop (nhds (d ^ 2)) := by
  have hshift := tendsto_shifted_degree_ratio_of_tendsto_ratio hu hratio
  have hmul := hratio.mul hshift
  have hlimit : Tendsto
      (fun n => (v n / u n) * ((1 + v n) / (1 + u n)))
      atTop (nhds (d ^ 2)) := by
    simpa [pow_two] using hmul
  apply hlimit.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  unfold quadraticCoordinate
  field_simp [hn.ne']
end MetricCodes.Spherical.HigherHierarchy
