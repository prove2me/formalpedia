-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonDelta_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/c95d1718-bdd6-4214-906c-fd879d5b8488

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonJ1_ratio
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_johnsonJ2_ratio

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
    {a b g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonDelta n (shellWeight a n)
          (supportDegree b n) (complementDegree g n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredEta a b g / 2)) := by
  have hmain :=
    (tendsto_johnsonJ2_ratio ha ha' hg).sub
      (tendsto_johnsonJ1_ratio ha hb)
  have hcenter :
      ((1 - a) / 2 - g) - (a / 2 - b) =
        MetricCodes.Johnson.centeredEta a b g / 2 := by
    unfold MetricCodes.Johnson.centeredEta
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonDelta
  ring
end MetricCodes.Johnson.SpectralAsymptotics
