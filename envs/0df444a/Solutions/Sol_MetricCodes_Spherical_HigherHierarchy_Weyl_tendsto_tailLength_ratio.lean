-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_tailLength_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/fd314d2d-e2b6-4a6e-a568-bd329e520910

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_nat_sequence_sub_cast_div
import Theorems.Thm_SpherePacking_tendsto_natCast_div_self

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
open Filter Topology
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution (r : ℕ) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => (tailLength n r i : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have h := SpherePacking.tendsto_nat_sequence_sub_cast_div
    (fun n : ℕ => n) (i.val + r + 3) 1 tendsto_id
    SpherePacking.tendsto_natCast_div_self
  refine h.congr' (Eventually.of_forall fun n => ?_)
  congr 2
  unfold tailLength
  omega
end MetricCodes.Spherical.HigherHierarchy.Weyl
