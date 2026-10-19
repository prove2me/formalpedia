-- Prove2me | solution 1 for MetricCodes.Numerics.kissing_sqrt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/2162262c-16ff-42e2-9dcc-2b762af22006

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
    Real.sqrt (kissingA * (1 + kissingA)) <
      (30503471040898065 : ℝ) / 10 ^ 17 := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) <
    (30503471040898065 : ℝ) / 10 ^ 17)).2
  norm_num [kissingA]
end MetricCodes.Numerics
