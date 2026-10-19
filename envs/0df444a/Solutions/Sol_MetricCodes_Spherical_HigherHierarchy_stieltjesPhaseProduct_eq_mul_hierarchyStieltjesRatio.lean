-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesPhaseProduct_eq_mul_hierarchyStieltjesRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/6de32472-4ab2-42aa-8372-1b9b7578910d

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
theorem _root_.solution
    {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) :
    stieltjesPhaseProduct a b t =
      t * hierarchyStieltjesRatio a b t := by
  unfold stieltjesPhaseProduct hierarchyStieltjesRatio
  ring
end MetricCodes.Spherical.HigherHierarchy
