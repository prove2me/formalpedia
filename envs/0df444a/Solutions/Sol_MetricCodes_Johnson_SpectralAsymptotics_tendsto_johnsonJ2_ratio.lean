-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonJ2_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/beb76e1d-0f8e-4a48-8032-8f4732e7319e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_complementDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_complementWeight_ratio

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
    {a g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ2 n (shellWeight a n) (complementDegree g n) /
          (n : ℝ))
      atTop (nhds ((1 - a) / 2 - g)) := by
  have hspin :=
    (tendsto_complementWeight_ratio ha ha').div_const 2
  have hmain := hspin.sub (tendsto_complementDegree_ratio hg)
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ2
  ring
end MetricCodes.Johnson.SpectralAsymptotics
