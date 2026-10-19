-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRateSet_nonempty_of_mem_source_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/99df8c1d-6304-4002-a779-047e7293d27a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_nonempty_of_interior

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
open Set Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s t : ℝ}
    (hs : 0 < s) (hs' : s < 1) (hts : t ≤ s) :
    (levelRateSet r t).Nonempty := by
  obtain ⟨R, a, b, h, hgap, hR⟩ :=
    levelRateSet_nonempty_of_interior r hs hs'
  exact ⟨R, a, b, h, lt_of_le_of_lt hts hgap, hR⟩
end MetricCodes.Spherical.HigherHierarchy
