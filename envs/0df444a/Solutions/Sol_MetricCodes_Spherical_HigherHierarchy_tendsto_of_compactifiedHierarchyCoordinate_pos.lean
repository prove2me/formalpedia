-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_of_compactifiedHierarchyCoordinate_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/88ed5342-8cd2-47da-bc63-a25d5c3bbbf4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactifiedHierarchyCoordinate_inv_sub_one

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
    {f : ℕ → ℝ} {x : ℝ}
    (hx : 0 < x)
    (h : Tendsto (fun k => compactifiedHierarchyCoordinate (f k))
      atTop (nhds x)) :
    Tendsto f atTop (nhds (x⁻¹ - 1)) := by
  have hi := h.inv₀ hx.ne'
  have hs :
      Tendsto
        (fun k : ℕ => (compactifiedHierarchyCoordinate (f k))⁻¹ - (1 : ℝ))
        atTop (nhds (x⁻¹ - 1)) :=
    hi.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  simpa only [compactifiedHierarchyCoordinate_inv_sub_one] using hs
end MetricCodes.Spherical.HigherHierarchy
