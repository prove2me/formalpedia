-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/033ebf01-9a85-4a85-b12f-60019f65fc52

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_codeNumber_pos
import Theorems.Thm_MetricCodes_Hamming_binaryRate_le_of_eventually
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_const_mul_bassalygoWindowFibreQuotient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
          C * bassalygoWindowFibreQuotient a b g u n) :
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.shellRate a b g u := by
  apply MetricCodes.Hamming.binaryRate_le_of_eventually
    (tendsto_logb_const_mul_bassalygoWindowFibreQuotient h hC)
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)]
    with n hcode hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcodepositive :
      0 < (MetricCodes.Hamming.codeNumber n
        (Nat.ceil (d * (n : ℝ))) : ℝ) := by
    exact_mod_cast MetricCodes.Hamming.codeNumber_pos n
      (Nat.ceil (d * (n : ℝ)))
  apply (div_le_div_iff_of_pos_right hnreal).mpr
  exact Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) hcodepositive hcode
end MetricCodes.Johnson.Asymptotics
