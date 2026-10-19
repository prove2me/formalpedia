-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactifiedHierarchyCoordinate_limit_pos_of_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/d717fafd-1b98-4860-bda4-aa905b04e2c5

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
    {f : ℕ → ℝ} {x C : ℝ}
    (hf : ∀ k, 0 ≤ f k)
    (hC : ∀ k, f k ≤ C)
    (h : Tendsto (fun k => compactifiedHierarchyCoordinate (f k))
      atTop (nhds x)) :
    0 < x := by
  have hC₀ : 0 ≤ C := (hf 0).trans (hC 0)
  have hCpos : 0 < 1 + C := by linarith
  have hlower : (1 + C)⁻¹ ≤ x := by
    apply ge_of_tendsto h
    exact Filter.Eventually.of_forall fun k =>
      (inv_le_inv₀ hCpos (by linarith [hf k])).mpr (by linarith [hC k])
  exact lt_of_lt_of_le (inv_pos.mpr hCpos) hlower
end MetricCodes.Spherical.HigherHierarchy
