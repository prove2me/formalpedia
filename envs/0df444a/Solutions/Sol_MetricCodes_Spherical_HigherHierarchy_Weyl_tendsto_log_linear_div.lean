-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Weyl.tendsto_log_linear_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/c54229f1-a15d-4a25-8c30-215fceb9da3b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_natCast_div_natCast

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
theorem _root_.solution {x : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hx : Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => Real.log (x n) / (n : ℝ))
      atTop (𝓝 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (x n / (n : ℝ)))
        atTop (𝓝 (Real.log c)) :=
    (Real.continuousAt_log hc.ne').tendsto.comp hx
  have hratio := hlog.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsum := hratio.add SpherePacking.tendsto_log_natCast_div_natCast
  have heq :
      (fun n : ℕ =>
        Real.log (x n / (n : ℝ)) * (n : ℝ)⁻¹ +
          Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (x n) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hx.eventually (Ioi_mem_nhds hc)] with n hn hxn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hxn' : x n / (n : ℝ) ≠ 0 := hxn.ne'
    rw [← div_eq_mul_inv, ← add_div,
      ← Real.log_mul hxn' hn', div_mul_cancel₀ _ hn']
  simpa using hsum.congr' heq
end MetricCodes.Spherical.HigherHierarchy.Weyl
