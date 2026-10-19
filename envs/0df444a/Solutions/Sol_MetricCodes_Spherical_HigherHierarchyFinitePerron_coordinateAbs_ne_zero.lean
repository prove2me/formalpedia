-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyFinitePerron.coordinateAbs_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/e5700ec6-ff1c-46cd-9602-470742d530e1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_coordinateAbs_norm

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
noncomputable section
set_option autoImplicit false
open Metric
open scoped BigOperators InnerProductSpace Matrix
open MetricCodes.Spherical.HigherHierarchyFinitePerron
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
namespace MetricCodes.Spherical.HigherHierarchyFinitePerron
theorem _root_.solution {x : Space I} (hx : x ≠ 0) :
    coordinateAbs x ≠ 0 := by
  intro habs
  have hnorm := coordinateAbs_norm x
  rw [habs, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)
end MetricCodes.Spherical.HigherHierarchyFinitePerron
