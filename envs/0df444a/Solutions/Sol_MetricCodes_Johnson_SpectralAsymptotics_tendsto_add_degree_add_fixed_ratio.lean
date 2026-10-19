-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_add_degree_add_fixed_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/2cf83188-9a64-4642-9b5a-251d98c742fa

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_add_degree_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (r : ℕ) :
    Tendsto
      (fun n : ℕ => ((f n + g n + r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a + b)) := by
  have hsum := tendsto_add_degree_ratio hf hg
  have hoffset :=
    tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have htotal := hsum.add hoffset
  rw [add_zero] at htotal
  refine htotal.congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring
end MetricCodes.Johnson.SpectralAsymptotics
