-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_bassalygoWindowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/9e221fda-e338-430e-b91b-86d522463676

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Hamming_eventually_windowFibreQuotient_pos
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_windowFibreQuotient
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_windowFibreQuotient_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_windowFibreQuotient
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_logb_bassalygoFactor

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
          (bassalygoWindowFibreQuotient a b g u n) / (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.shellRate a b g u)) := by
  have hfactor := tendsto_logb_bassalygoFactor h
  have hquotient := tendsto_logb_windowFibreQuotient h
  have hsum := hfactor.add hquotient
  have hlimit :
      (1 - MetricCodes.binaryEntropy a) +
          (MetricCodes.binaryEntropy u -
            MetricCodes.Johnson.rankPenalty a b g) =
        MetricCodes.Johnson.shellRate a b g u := by
    unfold MetricCodes.Johnson.shellRate
    ring
  rw [hlimit] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_windowFibreQuotient_pos h]
    with n hquotpos
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  have hfactorpos : 0 < bassalygoFactor a n := by
    unfold bassalygoFactor
    exact div_pos (by positivity) hchoosepos
  unfold bassalygoWindowFibreQuotient
  rw [Real.logb_mul hfactorpos.ne' hquotpos.ne']
  ring
end MetricCodes.Johnson.Asymptotics
