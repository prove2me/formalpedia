-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.eventually_bassalygoWindowFibreQuotient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/cb0eca97-4d11-4f48-b3b5-6c6834139f38

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Hamming_eventually_windowFibreQuotient_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_windowFibreQuotient_pos

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
    ∀ᶠ n : ℕ in atTop,
      0 < bassalygoWindowFibreQuotient a b g u n := by
  filter_upwards [eventually_windowFibreQuotient_pos h]
    with n hquot
  have hw : shellWeight a n ≤ n :=
    MetricCodes.Hamming.longitudinalDegree_le_dimension
      (by linarith [h.weight_lt_half]) n
  have hchoosepos : 0 < (n.choose (shellWeight a n) : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  unfold bassalygoWindowFibreQuotient bassalygoFactor
  exact mul_pos (div_pos (by positivity) hchoosepos) hquot
end MetricCodes.Johnson.Asymptotics
