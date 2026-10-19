-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_atTop_of_compactifiedHierarchyCoordinate_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/27139a93-8fed-4f6d-a3f2-0b05395e9eeb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k)
    (h : Tendsto (fun k => compactifiedHierarchyCoordinate (f k))
      atTop (nhds 0)) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro M
  let T : ℝ := max M 0
  have hT : 0 < 1 + T := by
    dsimp [T]
    linarith [le_max_right M 0]
  have hevent :
      ∀ᶠ k in atTop,
        compactifiedHierarchyCoordinate (f k) < (1 + T)⁻¹ :=
    (tendsto_order.1 h).2 _ (inv_pos.mpr hT)
  filter_upwards [hevent] with k hk
  have hfk : 0 < 1 + f k := by linarith [hf k]
  have hlt : T < f k := by
    have hinv : (1 + f k)⁻¹ < (1 + T)⁻¹ := hk
    have hraw : 1 + T < 1 + f k :=
      (inv_lt_inv₀ hfk hT).mp hinv
    linarith
  exact (le_max_left M 0).trans hlt.le
end MetricCodes.Spherical.HigherHierarchy
