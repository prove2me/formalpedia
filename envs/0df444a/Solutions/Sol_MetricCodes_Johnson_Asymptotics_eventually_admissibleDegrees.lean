-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.eventually_admissibleDegrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/0aa05534-8f70-40f2-a72f-3a19b505c48c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_shellWeight_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_supportDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_complementDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_terminalDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_dimension_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_add_degree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_degree_lt_of_ratio

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
    ∀ᶠ n : ℕ in atTop,
      MetricCodes.Johnson.AdmissibleDegrees n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n)
        (terminalDegree u n) := by
  have ha := h.weight_pos
  have hu := h.degree_pos
  have hw := tendsto_shellWeight_ratio ha.le
  have hp := tendsto_supportDegree_ratio h.support_nonneg
  have hq := tendsto_complementDegree_ratio h.complement_nonneg
  have hL := tendsto_terminalDegree_ratio hu.le
  have hn := tendsto_dimension_ratio
  have hww := tendsto_add_degree_ratio hw hw
  have hpp := tendsto_add_degree_ratio hp hp
  have hqq := tendsto_add_degree_ratio hq hq
  have hpq := tendsto_add_degree_ratio hp hq
  have hLp := tendsto_add_degree_ratio hL hp
  have hwq := tendsto_add_degree_ratio hw hq
  have hLw := tendsto_add_degree_ratio hL hw
  have hLwq := tendsto_add_degree_ratio hLw hq
  have hnp := tendsto_add_degree_ratio hn hp
  have hweight_positive :
      ∀ᶠ n : ℕ in atTop, 0 < shellWeight a n := by
    have hgrowth : Tendsto (shellWeight a) atTop atTop := by
      change Tendsto
        (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
      exact tendsto_nat_floor_mul_atTop a ha
    exact hgrowth.eventually (eventually_gt_atTop (0 : ℕ))
  have hweight_lt := eventually_degree_lt_of_ratio hw hn
    (by linarith [h.weight_lt_half])
  have hweight_half := eventually_degree_lt_of_ratio hww hn
    (by linarith [h.weight_lt_half])
  have hsupport_half := eventually_degree_lt_of_ratio hpp hw
    (by linarith [h.support_lt_half])
  have hcomplement_half := eventually_degree_lt_of_ratio
    (tendsto_add_degree_ratio hqq hw) hn
    (by linarith [h.complement_lt_half])
  have hfirst := eventually_degree_lt_of_ratio hpq hL
    h.first_lt_degree
  have hterminal_weight := eventually_degree_lt_of_ratio hL hw
    h.degree_lt_weight
  have hterminal_left := eventually_degree_lt_of_ratio hLp hwq
    (by linarith [h.degree_lt_left])
  have hterminal_right := eventually_degree_lt_of_ratio hLwq hnp
    (by linarith [h.degree_lt_right])
  filter_upwards [hweight_positive, hweight_lt, hweight_half,
    hsupport_half, hcomplement_half, hfirst,
    hterminal_weight, hterminal_left, hterminal_right]
    with n hpos hlt hhalf hsupport hcomplement
      hfirst' hweight' hleft hright
  refine {
    weight_pos := hpos
    weight_lt := hlt
    weight_half := by omega
    support_half := by omega
    complement_half := by omega
    first_le := by omega
    last_le := ?_
  }
  unfold MetricCodes.johnsonLastDegree
  apply le_min
  · omega
  · apply le_min <;> omega
end MetricCodes.Johnson.Asymptotics
