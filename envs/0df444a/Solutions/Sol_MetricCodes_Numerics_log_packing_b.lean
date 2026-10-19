-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/742d7bec-43fd-4261-8b2c-2400488d57db

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
    Real.log packingB = Real.log (256 * packingB) - 8 * Real.log 2 := by
  have hmul : Real.log (256 * packingB) =
      Real.log (256 : ℝ) + Real.log packingB :=
    Real.log_mul (by norm_num) (by norm_num [packingB])
  have hpow : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  rw [hpow] at hmul
  linarith
end MetricCodes.Numerics
