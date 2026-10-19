-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactificationCapFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/d30f7972-23c4-424c-8c78-1d48c34c177e

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
    0 < compactificationCapFactor s t := by
  unfold compactificationCapFactor
  apply Real.sqrt_pos.mpr
  exact div_pos (sub_pos.mpr hs)
    (sub_pos.mpr (lt_of_le_of_lt hts hs))
end MetricCodes.Spherical.HigherHierarchy
