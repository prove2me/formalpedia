-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_windowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/29905ae5-5645-42df-87ff-c16412dc0ebc

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AdmissibleDegrees_terminal_le_half
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_johnsonFibreDimension
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_terminalHarmonic_le_johnsonAmbientDimension
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_johnsonAmbientDimension

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
        Real.logb 2 (windowFibreQuotient a b g u n) / (n : ℝ))
      atTop
      (nhds (MetricCodes.binaryEntropy u -
        MetricCodes.Johnson.rankPenalty a b g)) := by
  have hnum := tendsto_logb_johnsonAmbientDimension h
  have hden := tendsto_logb_johnsonFibreDimension h
  have hdiff := hnum.sub hden
  refine hdiff.congr' ?_
  filter_upwards [eventually_admissibleDegrees h] with n hn
  have htermhalf : 2 * terminalDegree u n ≤ n := by
    have hhalf := hn.terminal_le_half
    omega
  have htermpos :
      0 < (MetricCodes.booleanHarmonicDimension n
        (terminalDegree u n) : ℝ) := by
    exact_mod_cast MetricCodes.Johnson.booleanHarmonicDimension_pos
      htermhalf
  have hambientpos :
      0 < (MetricCodes.johnsonAmbientDimension n
        (supportDegree b n + complementDegree g n)
        (terminalDegree u n) : ℝ) := by
    exact lt_of_lt_of_le htermpos
      (by exact_mod_cast terminalHarmonic_le_johnsonAmbientDimension hn)
  have hfibrepos :
      0 < (MetricCodes.johnsonFibreDimension n
        (shellWeight a n)
        (supportDegree b n)
        (complementDegree g n) : ℝ) := by
    exact_mod_cast hn.fibreDimension_pos
  unfold windowFibreQuotient
  rw [Real.logb_div hambientpos.ne' hfibrepos.ne']
  ring
end MetricCodes.Johnson.Asymptotics
