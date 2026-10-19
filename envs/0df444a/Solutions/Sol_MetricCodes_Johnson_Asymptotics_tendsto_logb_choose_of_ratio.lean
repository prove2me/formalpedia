-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_choose_of_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/b15bd795-956c-4aa9-9cd3-ca4894fff6c3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_add_choose_div
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_atTop_of_ratio_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_sub_degree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_scaled_binomialEntropy_identity

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
    {N K : ℕ → ℕ} {a b : ℝ}
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hK : Tendsto (fun n : ℕ => (K n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (hb : 0 < b) (hba : b < a)
    (hKN : ∀ᶠ n : ℕ in atTop, K n ≤ N n) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 ((N n).choose (K n) : ℝ) / (n : ℝ))
      atTop (nhds (a * MetricCodes.binaryEntropy (b / a))) := by
  have ha : 0 < a := lt_trans hb hba
  have hcomplement := tendsto_sub_degree_ratio hN hK hKN
  have hKgrowth := tendsto_atTop_of_ratio_pos hb hK
  have hcomplementgrowth :=
    tendsto_atTop_of_ratio_pos (sub_pos.mpr hba) hcomplement
  have hstirling := SpherePacking.tendsto_log_add_choose_div
    K (fun n : ℕ => N n - K n) b (a - b)
    hKgrowth hcomplementgrowth hK hcomplement
    hb (sub_pos.mpr hba)
  have hsum : b + (a - b) = a := by ring
  simp only [hsum] at hstirling
  have hbase := hstirling.div_const (Real.log 2)
  rw [scaled_binomialEntropy_identity ha hb hba] at hbase
  refine hbase.congr' ?_
  filter_upwards [hKN] with n hn
  have hinteger : K n + (N n - K n) = N n := by omega
  rw [hinteger]
  unfold Real.logb
  ring
end MetricCodes.Johnson.Asymptotics
