-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_logb_ambientDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/eacb05da-0e0e-47c5-b475-f669631cff09

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_transverse_add_le_longitudinal
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_choose_longitudinal
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_half
import Theorems.Thm_MetricCodes_Hamming_choose_le_ambientDimension
import Theorems.Thm_MetricCodes_Hamming_ambientDimension_le_mul_choose
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
theorem _root_.solution {a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a) (ha : a ≤ (1 : ℝ) / 2) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (ambientDimension n
            (transverseDegree b n) (longitudinalDegree a n) : ℝ) /
          (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a)) := by
  have ha0 : 0 < a := lt_of_le_of_lt hb hba
  have ha1 : a < 1 := lt_of_le_of_lt ha (by norm_num)
  have hchoose := tendsto_logb_choose_longitudinal ha0 ha1
  have hpoly := tendsto_logb_succ_div
  have hupperlim :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy a)) := by
    simpa using hpoly.add hchoose
  have hfit := eventually_transverse_add_le_longitudinal hb hba 0
  have hlower :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
          Real.logb 2
            (ambientDimension n (transverseDegree b n)
              (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
    filter_upwards [hfit, eventually_gt_atTop (0 : ℕ)] with n hkn hn
    have hkL : transverseDegree b n ≤ longitudinalDegree a n := by omega
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    · exact_mod_cast Nat.choose_pos
        (longitudinalDegree_le_dimension ha1.le n)
    · exact_mod_cast choose_le_ambientDimension n
        (transverseDegree b n) (longitudinalDegree a n) hkL
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2
            (ambientDimension n (transverseDegree b n)
              (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
    filter_upwards [hfit, eventually_gt_atTop (0 : ℕ)] with n hkn hn
    have hkL : transverseDegree b n ≤ longitudinalDegree a n := by omega
    have hhalf := longitudinalDegree_le_half ha n
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hchoosepos :
        0 < (n.choose (longitudinalDegree a n) : ℝ) := by
      exact_mod_cast Nat.choose_pos
        (longitudinalDegree_le_dimension ha1.le n)
    have hambientpos :
        0 < (ambientDimension n (transverseDegree b n)
          (longitudinalDegree a n) : ℝ) := by
      have hle := choose_le_ambientDimension n
        (transverseDegree b n) (longitudinalDegree a n) hkL
      exact lt_of_lt_of_le hchoosepos (by exact_mod_cast hle)
    calc
      Real.logb 2
          (ambientDimension n (transverseDegree b n)
            (longitudinalDegree a n) : ℝ) / (n : ℝ) ≤
        Real.logb 2
          (((n + 1) * n.choose (longitudinalDegree a n) : ℕ) : ℝ) /
            (n : ℝ) := by
          apply (div_le_div_iff_of_pos_right hnreal).2
          apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            hambientpos
          exact_mod_cast ambientDimension_le_mul_choose n
            (transverseDegree b n) (longitudinalDegree a n) hkL hhalf
      _ = Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) +
            Real.logb 2
              (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ) := by
          push_cast
          rw [Real.logb_mul (by positivity) hchoosepos.ne']
          ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hchoose hupperlim hlower hupper
end MetricCodes.Hamming
