-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_logb_windowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/f239e2b4-37ce-41b1-b59a-37571ee95eec

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_pos
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_half
import Theorems.Thm_MetricCodes_Hamming_choose_le_ambientDimension
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_ambientDimension
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_hammingFibreDimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a b : ℝ}
    (hb : 0 < b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ => Real.logb 2 (windowFibreQuotient a b n) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
  have hbhalf : b ≤ (1 : ℝ) / 2 := hba.le.trans ha
  have hnum := tendsto_logb_ambientDimension hb.le hba ha
  have hden := tendsto_logb_hammingFibreDimension hb hbhalf
  have hdiff := hnum.sub hden
  refine hdiff.congr' ?_
  filter_upwards [eventually_transverse_add_le_longitudinal hb.le hba 0]
    with n hfit
  have hkn : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hhalf := longitudinalDegree_le_half ha n
  have hkhalf : 2 * transverseDegree b n ≤ n := by omega
  have hfibre :
      0 < (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) := by
    exact_mod_cast hammingFibreDimension_pos hkhalf
  have haone : a ≤ 1 := by linarith
  have hchoose : 0 < (n.choose (longitudinalDegree a n) : ℝ) := by
    exact_mod_cast
      Nat.choose_pos (longitudinalDegree_le_dimension haone n)
  have hambient :
      0 < (ambientDimension n (transverseDegree b n)
        (longitudinalDegree a n) : ℝ) := by
    have hle := choose_le_ambientDimension n
      (transverseDegree b n) (longitudinalDegree a n) hkn
    exact lt_of_lt_of_le hchoose (by exact_mod_cast hle)
  unfold windowFibreQuotient
  rw [Real.logb_div hambient.ne' hfibre.ne']
  ring
end MetricCodes.Hamming
