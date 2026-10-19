-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_const_mul_bassalygoWindowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/d5821e28-ad20-40f5-964d-fa4bf302edf2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_bassalygoWindowFibreQuotient_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_bassalygoWindowFibreQuotient

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
    {d a b g u C : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2
          (C * bassalygoWindowFibreQuotient a b g u n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
  have hconstant :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)
  have hquotient := tendsto_logb_bassalygoWindowFibreQuotient h
  have hsum := hconstant.add hquotient
  have hsum' :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 C / (n : ℝ) +
            Real.logb 2
              (bassalygoWindowFibreQuotient a b g u n) /
                (n : ℝ))
        atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [eventually_bassalygoWindowFibreQuotient_pos h]
    with n hn
  rw [Real.logb_mul hC.ne' hn.ne']
  ring
end MetricCodes.Johnson.Asymptotics
