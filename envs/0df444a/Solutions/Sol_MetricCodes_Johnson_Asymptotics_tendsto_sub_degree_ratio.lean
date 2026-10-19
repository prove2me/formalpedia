-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_sub_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/935cea37-a2ea-4b53-b4ce-c77dd7598ec6

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
      atTop (nhds b))
    (hgf : ∀ᶠ n : ℕ in atTop, g n ≤ f n) :
    Tendsto
      (fun n : ℕ => ((f n - g n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a - b)) := by
  refine (hf.sub hg).congr' ?_
  filter_upwards [hgf] with n hn
  rw [Nat.cast_sub hn]
  ring
end MetricCodes.Johnson.Asymptotics
