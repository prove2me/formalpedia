-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_flooredCoordinates_succ_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/3d5ba442-cde1-4a34-ba27-eae854ce5dbe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_natCast_div_self
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_tendsto_flooredCoordinates_ratio

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
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {I : Type*}
    (a : I → ℝ) (i : I) (ha : 0 ≤ a i) :
    Tendsto
      (fun n : ℕ =>
        (flooredCoordinates a (n + 1) i : ℝ) / (n : ℝ))
      atTop (nhds (a i)) := by
  have hweight := (tendsto_flooredCoordinates_ratio a i ha).comp
    (tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (1 : ℝ)) := by
    have h := SpherePacking.tendsto_natCast_div_self.add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    convert h using 1
    · ext n
      push_cast
      ring
    · norm_num
  have hproduct := hweight.mul hratio
  have heq :
      (fun n : ℕ =>
        ((flooredCoordinates a (n + 1) i : ℝ) /
          ((n + 1 : ℕ) : ℝ)) *
            (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (flooredCoordinates a (n + 1) i : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hsucc : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa [Function.comp_def] using hproduct.congr' heq
end MetricCodes.Spherical.HigherHierarchy
