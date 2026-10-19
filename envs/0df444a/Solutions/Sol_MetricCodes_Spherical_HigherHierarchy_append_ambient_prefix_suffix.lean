-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.append_ambient_prefix_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/2e2fd06f-2a6a-4990-892f-3c83d6a916b4

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
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {k r : ℕ}
    (a : Fin (k + r + 1) → ℝ) :
    Fin.append (m := k) (n := r + 1)
        (fun i : Fin k => a (i.castAdd (r + 1)))
        (fun i : Fin (r + 1) => a (i.natAdd k)) = a := by
  funext i
  refine Fin.addCases (m := k) (n := r + 1) ?_ ?_ i
  · intro p
    simp
  · intro p
    simp
end MetricCodes.Spherical.HigherHierarchy
