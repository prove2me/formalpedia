-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_linearRowFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/8dd87444-a5e3-4523-b578-154ea0ad2235

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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Nat Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Weyl
namespace MetricCodes.Spherical.HigherHierarchy.Weyl
theorem _root_.solution
    (k : ℕ → ℕ) (c : ℕ) {a : ℝ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ =>
        (2 * (k n : ℝ) + (n : ℝ) - (c : ℝ)) /
          ((n : ℝ) - (c : ℝ)))
      atTop (𝓝 (2 * a + 1)) := by
  have hone := SpherePacking.tendsto_natCast_div_self
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)
  have hnum := ((hk.const_mul 2).add hone).sub hconst
  have hden := hone.sub hconst
  have hratio := hnum.div hden (by norm_num)
  have heq :
      (fun n : ℕ =>
        (2 * ((k n : ℝ) / (n : ℝ)) + (n : ℝ) / (n : ℝ) -
            (c : ℝ) / (n : ℝ)) /
          ((n : ℝ) / (n : ℝ) - (c : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (2 * (k n : ℝ) + (n : ℝ) - (c : ℝ)) /
          ((n : ℝ) - (c : ℝ))) := by
    filter_upwards [eventually_gt_atTop c] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le c) hn))
    have hnc : (n : ℝ) - (c : ℝ) ≠ 0 := by
      have h : (c : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    field_simp
  simpa using hratio.congr' heq
end MetricCodes.Spherical.HigherHierarchy.Weyl
