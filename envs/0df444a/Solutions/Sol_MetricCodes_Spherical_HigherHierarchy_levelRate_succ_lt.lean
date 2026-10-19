-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/ab212c79-4963-4e35-8489-8d2a9de5a37a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le_compactified_datum
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_succ_lt_of_compactified_positive_minimizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_positive_levelRate_minimizer

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
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    levelRate (r + 1) s < levelRate r s := by
  obtain ⟨j, c, a, b, hj, hc, hc', hdrop, h,
      hlast, hfeasible, hmin⟩ :=
    exists_compactified_positive_levelRate_minimizer (r := r) hs hs'
  exact levelRate_succ_lt_of_compactified_positive_minimizer
    hj hc hc' hdrop h hlast hfeasible hmin
    (fun A B hAB hstrict hlevels =>
      levelRate_le_compactified_datum hs hs' hc A B hAB hstrict hlevels)
end MetricCodes.Spherical.HigherHierarchy
