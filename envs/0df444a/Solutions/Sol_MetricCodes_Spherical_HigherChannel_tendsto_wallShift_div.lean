-- Prove2me | solution 1 for MetricCodes.Spherical.HigherChannel.tendsto_wallShift_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/279cf8e7-8b66-4cb4-a7a8-6675914b3ebe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
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
open MetricCodes.Spherical.HigherChannel
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherChannel
theorem _root_.solution (r : ℕ) :
    Tendsto (fun n : ℕ => wallShift n r / (n : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hdimension := SpherePacking.tendsto_natCast_div_self
  have hrow := tendsto_const_div_atTop_nhds_zero_nat ((r : ℝ) + 1)
  convert (hdimension.div_const (2 : ℝ)).sub hrow using 1
  · ext n
    simp only [wallShift, div_eq_mul_inv]
    ring
  · ring_nf
end MetricCodes.Spherical.HigherChannel
