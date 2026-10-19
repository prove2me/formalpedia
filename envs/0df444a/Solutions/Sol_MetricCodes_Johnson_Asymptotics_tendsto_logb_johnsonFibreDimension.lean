-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_johnsonFibreDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/26fc827c-d127-4823-bd12-76348be5cd28

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_supportHarmonicDimension
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_complementHarmonicDimension

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
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (MetricCodes.johnsonFibreDimension n
            (shellWeight a n)
            (supportDegree b n)
            (complementDegree g n) : ℝ) /
              (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.rankPenalty a b g)) := by
  have hsupport := tendsto_logb_supportHarmonicDimension h
  have hcomplement := tendsto_logb_complementHarmonicDimension h
  have hsum := hsupport.add hcomplement
  change
    Tendsto _ atTop
      (nhds
        (a * MetricCodes.binaryEntropy (b / a) +
          (1 - a) * MetricCodes.binaryEntropy (g / (1 - a))))
  refine hsum.congr' ?_
  filter_upwards [eventually_admissibleDegrees h]
    with n hn
  have hsupportpos :
      0 < (MetricCodes.booleanHarmonicDimension
        (shellWeight a n) (supportDegree b n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      hn.support_half
  have hcomplementpos :
      0 < (MetricCodes.booleanHarmonicDimension
        (n - shellWeight a n) (complementDegree g n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      hn.complement_half
  unfold MetricCodes.johnsonFibreDimension
  push_cast
  rw [Real.logb_mul hsupportpos.ne' hcomplementpos.ne']
  ring
end MetricCodes.Johnson.Asymptotics
