-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwRate_eq_objective_of_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/12394fc6-cf19-4feb-9a74-c3d981e3de54

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwRate_le_objective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ r : ℝ}
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      mrrwObjective δ r ≤ mrrwObjective δ s) :
    mrrwRate δ = mrrwObjective δ r := by
  apply le_antisymm
  · exact mrrwRate_le_objective hr hupper
  · unfold mrrwRate
    apply le_csInf
    · exact ⟨mrrwObjective δ r, r, hr, hupper, rfl⟩
    · rintro _ ⟨s, hs, hsupper, rfl⟩
      exact hmin s hs hsupper
end MetricCodes.Johnson
