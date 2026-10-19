-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.eventually_one_sub_threshold_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/8b1eca16-8461-49e6-bb4d-8c8571c52203

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_threshold_ceil
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_threshold_ceil

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
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      1 - MetricCodes.Johnson.threshold n (shellWeight a n)
        (Nat.ceil (d * (n : ℝ))) <
        2 - MetricCodes.Johnson.asymptoticThreshold d a := by
  have hlimit :
      MetricCodes.Johnson.asymptoticThreshold d a - 1 <
        MetricCodes.Johnson.asymptoticThreshold d a := by linarith
  have hthreshold :=
    (MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil h).eventually
      (Ioi_mem_nhds hlimit)
  filter_upwards [hthreshold] with n hn
  linarith
end MetricCodes.Johnson.SpectralAsymptotics
