-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeDenominator_append_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/424fa007-c567-40c9-befa-d614e448d204

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    lagrangeDenominator (appendAmbient a) i.castSucc =
      lagrangeDenominator a i * quadraticCoordinate (a i) := by
  unfold lagrangeDenominator appendAmbient
  rw [Fin.prod_univ_castSucc]
  simp [Fin.castSucc_succAbove_castSucc,
    Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i), quadraticCoordinate]
end MetricCodes.Spherical.HigherHierarchy
