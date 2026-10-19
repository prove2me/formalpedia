-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_atTop_of_ratio_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/a3e83452-452f-4ed4-ad38-088a85642d29

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    {f : ℕ → ℕ} {a : ℝ}
    (ha : 0 < a)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a)) :
    Tendsto f atTop atTop := by
  refine tendsto_atTop.2 fun m => ?_
  have hratio := hf.eventually (Ioi_mem_nhds (half_lt_self ha))
  have hgrowth :
      Tendsto (fun n : ℕ => (a / 2) * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos ha)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hratio' hlarge' hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfreal : (a / 2) * (n : ℝ) < (f n : ℝ) :=
    (lt_div_iff₀ hnreal).mp hratio'
  exact_mod_cast hlarge'.trans hfreal.le
end MetricCodes.Johnson.Asymptotics
