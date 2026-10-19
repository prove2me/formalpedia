-- Prove2me | solution 1 for MetricCodes.Numerics.packing_sqrt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/7829eeb8-d7ae-48da-8339-7f14babdf367

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
    Real.sqrt (packingA * (1 + packingA)) <
      (34177653924474340 : ℝ) / 10 ^ 17 := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) <
    (34177653924474340 : ℝ) / 10 ^ 17)).2
  norm_num [packingA]
end MetricCodes.Numerics
