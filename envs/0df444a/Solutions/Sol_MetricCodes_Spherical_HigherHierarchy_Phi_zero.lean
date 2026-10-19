-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/e01a45e5-82a6-4dd0-a231-2684c70628d8

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution (a : Fin 1 → ℝ) (b : Fin 0 → ℝ) :
    Phi a b = MetricCodes.sphericalEntropy (a 0) := by
  simp [Phi]
end MetricCodes.Spherical.HigherHierarchy
