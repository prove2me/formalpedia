-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.classicalHierarchyProfile_continuousOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/08abcb1a-99f1-4c09-b591-cce521005a7f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_continuous
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_continuousAt

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : s < 1) :
    ContinuousOn
      (fun t : ℝ => MetricCodes.sphericalEntropy
        (MetricCodes.classicalThreshold t))
      (Set.Icc (0 : ℝ) s) := by
  intro t ht
  exact
    (MetricCodes.Spherical.sphericalEntropy_continuous.continuousAt.comp
      (MetricCodes.Spherical.classicalThreshold_continuousAt
        (by linarith [ht.1]) (lt_of_le_of_lt ht.2 hs))).continuousWithinAt
end MetricCodes.Spherical.HigherHierarchy
