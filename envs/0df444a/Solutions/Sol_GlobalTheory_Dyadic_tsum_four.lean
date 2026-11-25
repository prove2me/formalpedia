-- Prove2me | solution 1 for GlobalTheory.Dyadic.tsum_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:41.001418+00:00
-- url     : https://prove2.me/submissions/6d0143d7-f26c-4fc9-be60-9f795fcc9502

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic
namespace GlobalTheory.Dyadic
theorem _root_.solution (C : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = C * 16 := by
  have h : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, h]
  norm_num
end GlobalTheory.Dyadic
