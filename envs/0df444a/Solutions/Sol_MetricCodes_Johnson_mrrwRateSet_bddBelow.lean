-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwRateSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/d840ac6b-bf13-42c4-bcfa-69ddb959ee03

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_binaryEntropy_le_one
import Theorems.Thm_MetricCodes_Johnson_binaryEntropy_le_one
import Theorems.Thm_MetricCodes_Johnson_mrrwG_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (δ : ℝ) :
    BddBelow (mrrwRateSet δ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, _hr, _hupper, rfl⟩
  have hfirst := mrrwG_nonneg (sq_nonneg r)
  have hsecond :
      mrrwG (r ^ 2 + 2 * δ * r + 2 * δ) ≤ 1 := by
    unfold mrrwG
    exact binaryEntropy_le_one _
  unfold mrrwObjective
  linarith
end MetricCodes.Johnson
