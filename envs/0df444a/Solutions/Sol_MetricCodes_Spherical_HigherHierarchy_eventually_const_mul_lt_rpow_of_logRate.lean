-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_const_mul_lt_rpow_of_logRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/b272dcf5-b48d-4366-9814-7e10d624be3c

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
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {q : ℕ → ℝ} {L R K : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop, 0 < q n)
    (hlim : Tendsto
      (fun n : ℕ => (Real.log (q n) / (n : ℝ)) / Real.log 2)
      atTop (nhds L))
    (hR : L < R) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, K * q n < (2 : ℝ) ^ (R * (n : ℝ)) := by
  have hconstant :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log K)).div_const
      (Real.log 2)
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (Real.log K / (n : ℝ)) / Real.log 2 +
            (Real.log (q n) / (n : ℝ)) / Real.log 2)
        atTop (nhds L) := by
    simpa using hconstant.add hlim
  have heq :
      (fun n : ℕ =>
        (Real.log K / (n : ℝ)) / Real.log 2 +
          (Real.log (q n) / (n : ℝ)) / Real.log 2) =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.log (K * q n) / (n : ℝ)) / Real.log 2) := by
    filter_upwards [hq] with n hn
    rw [Real.log_mul hK.ne' hn.ne']
    ring
  have hrate := (hsum.congr' heq).eventually (Iio_mem_nhds hR)
  filter_upwards [hrate, hq, eventually_gt_atTop (0 : ℕ)]
    with n hn hqn hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpositive : 0 < K * q n := mul_pos hK hqn
  have hlog : Real.log (K * q n) < (R * Real.log 2) * (n : ℝ) :=
    (div_lt_iff₀ hnreal).mp ((div_lt_iff₀ hlogtwo).mp hn)
  calc
    K * q n = Real.exp (Real.log (K * q n)) :=
      (Real.exp_log hpositive).symm
    _ < Real.exp (Real.log 2 * (R * (n : ℝ))) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    _ = (2 : ℝ) ^ (R * (n : ℝ)) :=
      (Real.rpow_def_of_pos (by norm_num) _).symm
end MetricCodes.Spherical.HigherHierarchy
