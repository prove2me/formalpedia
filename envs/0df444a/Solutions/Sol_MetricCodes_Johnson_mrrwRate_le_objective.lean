-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwRate_le_objective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/e40aaae5-aec7-44ae-b15f-a7edc5c8c385

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwRateSet_bddBelow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ) :
    mrrwRate δ ≤ mrrwObjective δ r := by
  exact csInf_le (mrrwRateSet_bddBelow δ)
    ⟨r, hr, hupper, rfl⟩
end MetricCodes.Johnson
