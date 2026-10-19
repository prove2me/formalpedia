-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/4cd93e2d-2602-425c-8c20-562fa18ebc53

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators
open MetricCodes.Numerics
namespace MetricCodes.Numerics
theorem _root_.solution :
    Real.log (2 / (1 - packingS)) =
      2 * Real.log 2 + Real.log (1 / (2 * (1 - packingS))) := by
  have hpow : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  calc
    Real.log (2 / (1 - packingS)) =
        Real.log (4 * (1 / (2 * (1 - packingS)))) := by
          congr 1
          norm_num [packingS]
    _ = Real.log (4 : ℝ) +
          Real.log (1 / (2 * (1 - packingS))) := by
            apply Real.log_mul
            · norm_num
            · norm_num [packingS]
    _ = 2 * Real.log 2 +
          Real.log (1 / (2 * (1 - packingS))) := by rw [hpow]
end MetricCodes.Numerics
