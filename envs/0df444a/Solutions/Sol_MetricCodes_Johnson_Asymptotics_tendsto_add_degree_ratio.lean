-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_add_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/f01885df-29ff-45e6-b9fb-d0dff183233e

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
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b)) :
    Tendsto
      (fun n : ℕ => ((f n + g n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a + b)) := by
  refine (hf.add hg).congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring
end MetricCodes.Johnson.Asymptotics
