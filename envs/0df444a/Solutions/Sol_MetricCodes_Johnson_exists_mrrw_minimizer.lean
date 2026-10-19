-- Prove2me | solution 1 for MetricCodes.Johnson.exists_mrrw_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/1e468931-0ea7-4f2c-af5f-99005aae39e3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwObjective_continuous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ : ℝ}
    (hhalf : δ ≤ (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 - 2 * δ ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        mrrwObjective δ r ≤ mrrwObjective δ s := by
  have hnonempty : (Set.Icc 0 (1 - 2 * δ)).Nonempty := by
    refine ⟨0, ?_⟩
    constructor
    · exact le_rfl
    · linarith
  obtain ⟨r, hr, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hnonempty
      (mrrwObjective_continuous δ).continuousOn
  refine ⟨r, hr.1, hr.2, ?_⟩
  intro s hs hupper
  exact hmin ⟨hs, hupper⟩
end MetricCodes.Johnson
