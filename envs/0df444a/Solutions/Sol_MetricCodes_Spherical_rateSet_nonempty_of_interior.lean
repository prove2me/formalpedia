-- Prove2me | solution 1 for MetricCodes.Spherical.rateSet_nonempty_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/e6f3b6c6-140a-439a-b60e-b1ea099fdbf3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_exists_strict_improving_spherical_feasible

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (rateSet s).Nonempty := by
  obtain ⟨a, b, hf, _⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  exact ⟨MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b,
    a, b, hf, rfl⟩
end MetricCodes.Spherical
