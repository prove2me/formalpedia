-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwG_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/9bd6d13f-ca51-4982-9127-c4c8c9f78c06

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {u : ℝ}
    (hu : u ≤ (1 : ℝ) / 2) :
    mrrwG (4 * u * (1 - u)) = MetricCodes.binaryEntropy u := by
  have hrad :
      1 - 4 * u * (1 - u) = (1 - 2 * u) ^ 2 := by
    ring
  have hroot :
      Real.sqrt (1 - 4 * u * (1 - u)) = 1 - 2 * u := by
    rw [hrad, Real.sqrt_sq (by linarith)]
  unfold mrrwG
  rw [hroot]
  congr 1
  ring
end MetricCodes.Johnson
