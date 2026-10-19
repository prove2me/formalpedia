-- Prove2me | solution 1 for MetricCodes.Numerics.kissing_entropy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/ebccb6b5-647d-4700-b194-afc7dacab58e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_two_interval
import Theorems.Thm_MetricCodes_Numerics_log_kissing_one_add_a_interval
import Theorems.Thm_MetricCodes_Numerics_log_kissing_scaled_a_interval
import Theorems.Thm_MetricCodes_Numerics_log_kissing_one_add_b_interval
import Theorems.Thm_MetricCodes_Numerics_log_kissing_inverse_scaled_b_interval
import Theorems.Thm_MetricCodes_Numerics_log_kissing_a
import Theorems.Thm_MetricCodes_Numerics_log_kissing_b

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    MetricCodes.sphericalEntropy kissingA - MetricCodes.sphericalEntropy kissingB <
      (0.397305601680 : ℝ) := by
  have htwo := log_two_interval.1
  have h1a := log_kissing_one_add_a_interval.2
  have hsa := log_kissing_scaled_a_interval.1
  have h1b := log_kissing_one_add_b_interval.1
  have hib := log_kissing_inverse_scaled_b_interval.1
  have hmain :
      (1 + kissingA) * Real.log (1 + kissingA) -
          kissingA * (Real.log (16 * kissingA) - 4 * Real.log 2) -
          ((1 + kissingB) * Real.log (1 + kissingB) -
            kissingB *
              (-8 * Real.log 2 - Real.log (1 / (256 * kissingB)))) <
        (0.397305601680 : ℝ) * Real.log 2 := by
    norm_num [kissingA, kissingB] at htwo h1a hsa h1b hib ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    MetricCodes.sphericalEntropy kissingA - MetricCodes.sphericalEntropy kissingB =
        ((1 + kissingA) * Real.log (1 + kissingA) -
          kissingA * Real.log kissingA -
          ((1 + kissingB) * Real.log (1 + kissingB) -
            kissingB * Real.log kissingB)) / Real.log 2 := by
          unfold MetricCodes.sphericalEntropy Real.logb
          ring
    _ < (0.397305601680 : ℝ) := by
      apply (div_lt_iff₀ hlog).2
      rw [log_kissing_a, log_kissing_b]
      exact hmain
end MetricCodes.Numerics
