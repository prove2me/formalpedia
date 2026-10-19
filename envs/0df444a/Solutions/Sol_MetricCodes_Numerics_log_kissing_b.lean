-- Prove2me | solution 1 for MetricCodes.Numerics.log_kissing_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/2d536b01-7db8-438f-ba18-0ddca0fc2418

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
    Real.log kissingB =
      -8 * Real.log 2 - Real.log (1 / (256 * kissingB)) := by
  have hmul : Real.log (256 * kissingB) =
      Real.log (256 : ℝ) + Real.log kissingB :=
    Real.log_mul (by norm_num) (by norm_num [kissingB])
  have hpow : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  have hinv : Real.log (1 / (256 * kissingB)) =
      -Real.log (256 * kissingB) := by
    rw [one_div, Real.log_inv]
  rw [hpow] at hmul
  linarith
end MetricCodes.Numerics
