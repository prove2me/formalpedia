-- Prove2me | solution 1 for MetricCodes.MRRW.mrrw_minimizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/2720b7f7-131a-43fe-bdcc-98a7658d1b77

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_exists_mrrwObjective_lt_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ r : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      MetricCodes.Johnson.mrrwObjective δ r ≤
        MetricCodes.Johnson.mrrwObjective δ s) :
    0 < r := by
  rcases hr.eq_or_lt with hzero | hpositive
  · have hrzero : r = 0 := hzero.symm
    subst r
    obtain ⟨s, hs, hsupper, hstrict⟩ :=
      exists_mrrwObjective_lt_zero hδ hhalf
    exact False.elim
      ((not_lt_of_ge (hmin s hs.le hsupper.le)) hstrict)
  · exact hpositive
end MetricCodes.MRRW
