-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_dimension_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/7bab1b83-09cf-4358-aef5-ff7bf4bde397

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
theorem _root_.solution :
    Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds (1 : ℝ)) := by
  refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  simp [hn]
end MetricCodes.Johnson.Asymptotics
