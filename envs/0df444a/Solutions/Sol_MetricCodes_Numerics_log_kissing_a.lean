-- Prove2me | solution 1 for MetricCodes.Numerics.log_kissing_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/7c7b6cbc-c03c-4d24-81aa-fc97a6138a86

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
    Real.log kissingA = Real.log (16 * kissingA) - 4 * Real.log 2 := by
  have hmul : Real.log (16 * kissingA) =
      Real.log (16 : ℝ) + Real.log kissingA :=
    Real.log_mul (by norm_num) (by norm_num [kissingA])
  have hpow : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  rw [hpow] at hmul
  linarith
end MetricCodes.Numerics
