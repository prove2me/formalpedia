-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactificationCapFactor_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/fa9db575-d7d4-4f2c-9b34-a01400c26c1b

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s t : ℝ} (hs : s < 1) (hts : t ≤ s) :
    compactificationCapFactor s t ^ 2 =
      (1 - s) / (1 - t) := by
  unfold compactificationCapFactor
  exact Real.sq_sqrt
    (div_nonneg (sub_nonneg.mpr hs.le)
      (sub_nonneg.mpr (le_trans hts hs.le)))
end MetricCodes.Spherical.HigherHierarchy
