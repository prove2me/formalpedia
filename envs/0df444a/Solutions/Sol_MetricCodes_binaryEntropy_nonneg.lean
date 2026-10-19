-- Prove2me | solution 1 for MetricCodes.binaryEntropy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/a52cf325-33d7-48e2-b9ab-88e3ac456d1c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators InnerProductSpace
namespace MetricCodes
theorem _root_.solution {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    0 ≤ binaryEntropy u := by
  have h₁ : Real.logb 2 u ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu hu'
  have h₂ : Real.logb 2 (1 - u) ≤ 0 :=
    Real.logb_nonpos (by norm_num : (1 : ℝ) < 2)
      (by linarith) (by linarith)
  unfold binaryEntropy
  have hleft : u * Real.logb 2 u ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hu h₁
  have hright : (1 - u) * Real.logb 2 (1 - u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) h₂
  linarith
end MetricCodes
