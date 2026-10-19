-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_shifted_degree_ratio_of_tendsto_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/bf328ca2-41c9-4a7b-beca-6d399a45f5da

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {u v : ℕ → ℝ} {d : ℝ}
    (hu : Tendsto u atTop atTop)
    (hratio : Tendsto (fun n => v n / u n) atTop (nhds d)) :
    Tendsto (fun n => (1 + v n) / (1 + u n))
      atTop (nhds d) := by
  have hinv : Tendsto (fun n => (u n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hnormalized :
      Tendsto (fun n => ((u n)⁻¹ + v n / u n) /
        ((u n)⁻¹ + 1)) atTop (nhds d) := by
    convert (hinv.add hratio).div (hinv.add_const 1)
      (by norm_num : (0 : ℝ) + 1 ≠ 0) using 1
    · ext n
      rfl
    · norm_num
  apply hnormalized.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn
  field_simp
end MetricCodes.Spherical.HigherHierarchy
