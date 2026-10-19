-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_bassalygoFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/5a989901-d82d-455a-85eb-b0fda60e7b7e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_dimension_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_shellChoose

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
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (bassalygoFactor a n) / (n : ℝ))
      atTop (nhds (1 - MetricCodes.binaryEntropy a)) := by
  have hpower :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ))
        atTop (nhds (1 : ℝ)) := by
    refine tendsto_dimension_ratio.congr'
      (Eventually.of_forall fun n => ?_)
    change
      (n : ℝ) / (n : ℝ) =
        Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    simp
  have hchoose := tendsto_logb_shellChoose h
  have hdiff := hpower.sub hchoose
  refine hdiff.congr' (Eventually.of_forall fun n => ?_)
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  unfold bassalygoFactor
  change
    Real.logb 2 ((2 : ℝ) ^ n) / (n : ℝ) -
        Real.logb 2 (n.choose (shellWeight a n) : ℝ) / (n : ℝ) =
      Real.logb 2
        (((2 : ℝ) ^ n) / (n.choose (shellWeight a n) : ℝ)) /
          (n : ℝ)
  rw [Real.logb_div (by positivity) hchoosepos.ne']
  ring
end MetricCodes.Johnson.Asymptotics
