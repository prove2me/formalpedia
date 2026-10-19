-- Prove2me | solution 1 for MetricCodes.MRRW.exists_positive_mrrw_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/26a40b83-053f-456f-9ab1-95218bb113d4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_exists_mrrw_minimizer
import Theorems.Thm_MetricCodes_Johnson_mrrwRate_eq_objective_of_minimizer
import Theorems.Thm_MetricCodes_MRRW_mrrw_minimizer_pos

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
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 - 2 * δ ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        MetricCodes.Johnson.mrrwObjective δ r ≤
          MetricCodes.Johnson.mrrwObjective δ s) ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.mrrwObjective δ r := by
  obtain ⟨r, hr, hupper, hmin⟩ :=
    MetricCodes.Johnson.exists_mrrw_minimizer hhalf.le
  refine ⟨r, mrrw_minimizer_pos hδ hhalf hr hupper hmin,
    hupper, hmin, ?_⟩
  exact MetricCodes.Johnson.mrrwRate_eq_objective_of_minimizer
    hr hupper hmin
end MetricCodes.MRRW
