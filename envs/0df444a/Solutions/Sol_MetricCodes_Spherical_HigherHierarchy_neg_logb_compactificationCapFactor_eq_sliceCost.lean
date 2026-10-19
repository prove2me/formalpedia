-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.neg_logb_compactificationCapFactor_eq_sliceCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/2f466f92-9d1c-4eee-8d5a-0042247264ef

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
    -Real.logb 2 (compactificationCapFactor s t) =
      MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
  have ht : t < 1 := lt_of_le_of_lt hts hs
  have hratio : 0 ≤ (1 - s) / (1 - t) := by
    exact div_nonneg (sub_nonneg.mpr hs.le) (sub_nonneg.mpr ht.le)
  unfold compactificationCapFactor
    MetricCodes.Spherical.SidelnikovLocalization.sliceCost Real.logb
  rw [Real.log_sqrt hratio]
  rw [Real.log_div (by linarith : 1 - s ≠ 0)
    (by linarith : 1 - t ≠ 0),
    Real.log_div (by linarith : 1 - t ≠ 0)
      (by linarith : 1 - s ≠ 0)]
  ring
end MetricCodes.Spherical.HigherHierarchy
