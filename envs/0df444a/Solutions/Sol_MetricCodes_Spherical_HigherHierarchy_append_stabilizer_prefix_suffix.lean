-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.append_stabilizer_prefix_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/d690d2f6-3078-45b8-959a-ec246b44137b

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
    (b : Fin (k + r) → ℝ) :
    Fin.append (m := k) (n := r)
        (fun i : Fin k => b (i.castAdd r))
        (fun i : Fin r => b (i.natAdd k)) = b := by
  funext i
  refine Fin.addCases (m := k) (n := r) ?_ ?_ i
  · intro p
    simp
  · intro p
    simp
end MetricCodes.Spherical.HigherHierarchy
