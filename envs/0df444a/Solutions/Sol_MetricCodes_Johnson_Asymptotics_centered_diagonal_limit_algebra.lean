-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.centered_diagonal_limit_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/a48dff21-9d57-474b-ba2d-915a71c1c3d9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {a m sigma eta z : ℝ}
    (hz : z ≠ 0)
    (hm : 1 - m ^ 2 ≠ 0)
    (hcenter : 1 - m ^ 2 = 4 * a * (1 - a)) :
    (m * sigma * eta / (4 * z ^ 2) - (m / 2) ^ 2) /
        (a * (1 - a)) =
      m * (sigma * eta - m * z ^ 2) /
        (z ^ 2 * (1 - m ^ 2)) := by
  have hprod : a * (1 - a) ≠ 0 := by
    intro hzero
    apply hm
    rw [hcenter]
    calc
      4 * a * (1 - a) = 4 * (a * (1 - a)) := by ring
      _ = 0 := by rw [hzero]; ring
  have ha : a ≠ 0 := by
    intro hzero
    apply hprod
    simp [hzero]
  have ha' : 1 - a ≠ 0 := by
    intro hzero
    apply hprod
    rw [hzero]
    ring
  rw [hcenter]
  field_simp [hz, ha, ha']
  ; ring
end MetricCodes.Johnson.Asymptotics
