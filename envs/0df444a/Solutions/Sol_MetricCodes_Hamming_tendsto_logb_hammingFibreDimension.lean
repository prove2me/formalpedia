-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_logb_hammingFibreDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/9c8ea393-372c-48e3-a05a-050252593925

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_pos
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_choose_longitudinal
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_half
import Theorems.Thm_MetricCodes_Hamming_choose_le_mul_hammingFibreDimension
import Theorems.Thm_MetricCodes_Hamming_hammingFibreDimension_le_choose
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_succ_div

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {b : ℝ}
    (hb : 0 < b) (hb' : b ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.hammingFibreDimension n (transverseDegree b n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy b)) := by
  have hb1 : b < 1 := lt_of_le_of_lt hb' (by norm_num)
  have hchoose :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa [transverseDegree, longitudinalDegree] using
      tendsto_logb_choose_longitudinal hb hb1
  have hpoly := tendsto_logb_succ_div
  have hlowerlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy b)) := by
    simpa using hchoose.sub hpoly
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
              (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
            Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa [transverseDegree, longitudinalDegree] using
          longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    have hchoosepos : 0 < (n.choose (transverseDegree b n) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : transverseDegree b n ≤ n)
    have hlog :
        Real.logb 2 (n.choose (transverseDegree b n) : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) +
            Real.logb 2
              (MetricCodes.hammingFibreDimension n
                (transverseDegree b n) : ℝ) := by
      rw [← Real.logb_mul (by positivity) hfibre.ne']
      apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        hchoosepos
      exact_mod_cast choose_le_mul_hammingFibreDimension hkhalf
    calc
      Real.logb 2 (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) =
        (Real.logb 2 (n.choose (transverseDegree b n) : ℝ) -
          Real.logb 2 ((n + 1 : ℕ) : ℝ)) / (n : ℝ) := by ring
      _ ≤ Real.logb 2
          (MetricCodes.hammingFibreDimension n
            (transverseDegree b n) : ℝ) / (n : ℝ) := by
        apply (div_le_div_iff_of_pos_right hnreal).2
        linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (MetricCodes.hammingFibreDimension n
              (transverseDegree b n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (n.choose (transverseDegree b n) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hkhalf : 2 * transverseDegree b n ≤ n := by
      have h : transverseDegree b n ≤ n / 2 := by
        simpa [transverseDegree, longitudinalDegree] using
          longitudinalDegree_le_half hb' n
      omega
    have hfibre :
        0 < (MetricCodes.hammingFibreDimension n
          (transverseDegree b n) : ℝ) := by
      exact_mod_cast hammingFibreDimension_pos hkhalf
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      hfibre
    exact_mod_cast hammingFibreDimension_le_choose n
      (transverseDegree b n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlim hchoose hlower hupper
end MetricCodes.Hamming
