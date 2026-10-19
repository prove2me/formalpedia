-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.oneRowBoundaryObjective_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/8fb87a0a-65e6-41ba-8bd9-43578dd51b35

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous

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
theorem _root_.solution (s : ℝ) :
    Continuous (fun a : ℝ => oneRowBoundaryObjective s a) := by
  have hquadratic :
      Continuous (fun a : ℝ =>
        MetricCodes.Spherical.boundaryQuadratic s a) := by
    unfold MetricCodes.Spherical.boundaryQuadratic
    fun_prop
  have hdegree :
      Continuous (fun a : ℝ => MetricCodes.Spherical.boundaryDegree s a) := by
    unfold MetricCodes.Spherical.boundaryDegree
    fun_prop
  exact MetricCodes.Spherical.sphericalEntropy_continuous.sub
    (MetricCodes.Spherical.sphericalEntropy_continuous.comp hdegree)
end MetricCodes.Spherical.HigherHierarchy
