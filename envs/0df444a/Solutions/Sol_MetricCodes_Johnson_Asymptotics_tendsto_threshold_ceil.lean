-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/c9db96b1-b8a6-4978-8abd-369f5891cc5e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_ceil_distance_ratio
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_weight_complement_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_shellWeight_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_complementShellWeight_ratio

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
        MetricCodes.Johnson.threshold n (shellWeight a n)
          (Nat.ceil (d * (n : ℝ))))
      atTop (nhds (MetricCodes.Johnson.asymptoticThreshold d a)) := by
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementShellWeight_ratio
    h.weight_pos.le (by linarith [h.weight_lt_half])
  have hd := MetricCodes.Hamming.tendsto_ceil_distance_ratio
    h.distance_pos.le
  have hden :=
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hw).mul hc
  have hdenpos : 0 < 2 * a * (1 - a) := by
    have ha := h.weight_pos
    have hc' := h.weight_complement_pos
    positivity
  have hdivision := hd.div hden hdenpos.ne'
  have hnormalized :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub hdivision
  have hnormalized' :
      Tendsto
        (fun n : ℕ =>
          1 -
            (((Nat.ceil (d * (n : ℝ)) : ℕ) : ℝ) /
              (n : ℝ)) /
              (2 * ((shellWeight a n : ℝ) / (n : ℝ)) *
                (((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))))
        atTop (nhds (MetricCodes.Johnson.asymptoticThreshold d a)) := by
    simpa [MetricCodes.Johnson.asymptoticThreshold] using hnormalized
  refine hnormalized'.congr' ?_
  filter_upwards [eventually_admissibleDegrees h,
    eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hwreal : (0 : ℝ) < (shellWeight a n : ℝ) := by
    exact_mod_cast hn.weight_pos
  have hcreal :
      (0 : ℝ) < ((n - shellWeight a n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - shellWeight a n by
      exact Nat.sub_pos_of_lt hn.weight_lt)
  unfold MetricCodes.Johnson.threshold
  field_simp [hnreal.ne', hwreal.ne', hcreal.ne']
end MetricCodes.Johnson.Asymptotics
