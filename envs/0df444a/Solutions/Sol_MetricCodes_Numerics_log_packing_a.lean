-- Prove2me | solution 1 for MetricCodes.Numerics.log_packing_a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/6226e7d1-61b6-464e-94c2-8914023b47b0

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
    Real.log packingA =
      -3 * Real.log 2 - Real.log (1 / (8 * packingA)) := by
  have hmul : Real.log (8 * packingA) =
      Real.log (8 : ℝ) + Real.log packingA :=
    Real.log_mul (by norm_num) (by norm_num [packingA])
  have hpow : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1 <;> norm_num
  have hinv : Real.log (1 / (8 * packingA)) =
      -Real.log (8 * packingA) := by
    rw [one_div, Real.log_inv]
  rw [hpow] at hmul
  linarith
end MetricCodes.Numerics
