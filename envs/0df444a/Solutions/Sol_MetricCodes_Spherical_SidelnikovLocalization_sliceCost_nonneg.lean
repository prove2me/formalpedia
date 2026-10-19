-- Prove2me | solution 1 for MetricCodes.Spherical.SidelnikovLocalization.sliceCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/46633ecd-458d-46ed-b8a5-a8a99114a55f

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
noncomputable section
open scoped InnerProductSpace Topology
open MetricCodes.Spherical.SidelnikovLocalization
namespace MetricCodes.Spherical.SidelnikovLocalization
theorem _root_.solution {s t : ℝ}
    (hts : t ≤ s) (hs : s < 1) :
    0 ≤ sliceCost s t := by
  unfold sliceCost
  apply mul_nonneg (by norm_num)
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  exact (le_div_iff₀ (by linarith)).2 (by linarith)
end MetricCodes.Spherical.SidelnikovLocalization
