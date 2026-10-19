-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_johnsonM_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/9fbc63ae-bfd0-4d1f-9042-1cae36bd3333

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_shellWeight_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_dimension_ratio

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
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredWeight a / 2)) := by
  have hspin := tendsto_dimension_ratio.div_const 2
  have hmain := hspin.sub (tendsto_shellWeight_ratio ha)
  have hcenter : (1 : ℝ) / 2 - a =
      MetricCodes.Johnson.centeredWeight a / 2 := by
    unfold MetricCodes.Johnson.centeredWeight
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonM
  ring
end MetricCodes.Johnson.SpectralAsymptotics
