-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_of_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/843feeb2-840c-4cbe-8d86-bfbd9f7b0311

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyRateSet_bddBelow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {s : ℝ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hgap : s < 2 * Gamma a b) :
    hierarchyVariationalRate s ≤ Phi a b := by
  exact csInf_le (hierarchyRateSet_bddBelow s)
    ⟨r, a, b, h, hgap, rfl⟩
end MetricCodes.Spherical.HigherHierarchy
