-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.oneRowBoundaryObjective_joint_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/34eb9a8e-edb8-4b99-8f1c-08d086626226

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
open Set Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution :
    Continuous (fun p : ℝ × ℝ => oneRowBoundaryObjective p.1 p.2) := by
  have hdegree : Continuous
      (fun p : ℝ × ℝ => MetricCodes.Spherical.boundaryDegree p.1 p.2) := by
    unfold MetricCodes.Spherical.boundaryDegree
      MetricCodes.Spherical.boundaryQuadratic
    fun_prop
  exact (MetricCodes.Spherical.sphericalEntropy_continuous.comp
    continuous_snd).sub
      (MetricCodes.Spherical.sphericalEntropy_continuous.comp hdegree)
end MetricCodes.Spherical.HigherHierarchy
