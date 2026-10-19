-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonJ1_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/671ccc8b-1efd-4980-997c-52c3e348bb42

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_shellWeight_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_supportDegree_ratio

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
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ1 (shellWeight a n) (supportDegree b n) /
          (n : ℝ))
      atTop (nhds (a / 2 - b)) := by
  have hspin :=
    (tendsto_shellWeight_ratio ha).div_const 2
  have hmain := hspin.sub (tendsto_supportDegree_ratio hb)
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ1
  ring
end MetricCodes.Johnson.SpectralAsymptotics
