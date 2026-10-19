-- Prove2me | solution 1 for MetricCodes.Johnson.variationalRate_le_of_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/83107704-ed9d-4f7c-b603-da94822055e9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_rateSet_bddBelow
import Theorems.Thm_MetricCodes_Johnson_rateSet_bddBelow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ α β γ u : ℝ}
    (h : Feasible δ α β γ u) :
    variationalRate δ ≤ shellRate α β γ u := by
  exact csInf_le (rateSet_bddBelow δ) ⟨α, β, γ, u, h, rfl⟩
end MetricCodes.Johnson
