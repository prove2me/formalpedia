-- Prove2me | solution 1 for MetricCodes.Numerics.packing_entropy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/9c1436af-c09b-44b9-9b8c-e6f435091cd1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_two_interval
import Theorems.Thm_MetricCodes_Numerics_log_packing_one_add_a_interval
import Theorems.Thm_MetricCodes_Numerics_log_packing_inverse_scaled_a_interval
import Theorems.Thm_MetricCodes_Numerics_log_packing_one_add_b_interval
import Theorems.Thm_MetricCodes_Numerics_log_packing_scaled_b_interval
import Theorems.Thm_MetricCodes_Numerics_log_packing_geometric_interval
import Theorems.Thm_MetricCodes_Numerics_log_packing_a
import Theorems.Thm_MetricCodes_Numerics_log_packing_b
import Theorems.Thm_MetricCodes_Numerics_log_packing_geometric

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    (0.602872829455 : ℝ) <
      (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - packingS)) -
        MetricCodes.sphericalEntropy packingA + MetricCodes.sphericalEntropy packingB := by
  have htwo := log_two_interval.1
  have hgeo := log_packing_geometric_interval.1
  have h1a := log_packing_one_add_a_interval.2
  have hia := log_packing_inverse_scaled_a_interval.2
  have h1b := log_packing_one_add_b_interval.1
  have hsb := log_packing_scaled_b_interval.2
  have hmain :
      (0.602872829455 : ℝ) * Real.log 2 <
        (1 / 2 : ℝ) *
            (2 * Real.log 2 + Real.log (1 / (2 * (1 - packingS)))) -
          ((1 + packingA) * Real.log (1 + packingA) -
            packingA *
              (-3 * Real.log 2 - Real.log (1 / (8 * packingA)))) +
          ((1 + packingB) * Real.log (1 + packingB) -
            packingB * (Real.log (256 * packingB) - 8 * Real.log 2)) := by
    norm_num [packingS, packingA, packingB]
      at htwo hgeo h1a hia h1b hsb ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (0.602872829455 : ℝ) <
        ((1 / 2 : ℝ) * Real.log (2 / (1 - packingS)) -
          ((1 + packingA) * Real.log (1 + packingA) -
            packingA * Real.log packingA) +
          ((1 + packingB) * Real.log (1 + packingB) -
            packingB * Real.log packingB)) / Real.log 2 := by
            apply (lt_div_iff₀ hlog).2
            rw [log_packing_geometric, log_packing_a, log_packing_b]
            exact hmain
    _ = (1 / 2 : ℝ) * Real.logb 2 (2 / (1 - packingS)) -
        MetricCodes.sphericalEntropy packingA +
          MetricCodes.sphericalEntropy packingB := by
            unfold MetricCodes.sphericalEntropy Real.logb
            ring
end MetricCodes.Numerics
