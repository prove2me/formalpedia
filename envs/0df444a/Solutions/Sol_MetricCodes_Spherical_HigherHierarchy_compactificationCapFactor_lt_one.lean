-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactificationCapFactor_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/4f9c9d65-de73-40d7-a222-924ffd363567

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactificationCapFactor_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactificationCapFactor_sq

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
    {s t : ℝ} (hs : s < 1) (hts : t < s) :
    compactificationCapFactor s t < 1 := by
  have hden : 0 < 1 - t := by linarith
  have hratio : (1 - s) / (1 - t) < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hsq := compactificationCapFactor_sq hs hts.le
  have hnonneg : 0 ≤ compactificationCapFactor s t :=
    (compactificationCapFactor_pos hs hts.le).le
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
