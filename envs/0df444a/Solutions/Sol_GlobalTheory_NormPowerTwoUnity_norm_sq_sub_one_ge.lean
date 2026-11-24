-- Prove2me | solution 1 for GlobalTheory.NormPowerTwoUnity.norm_sq_sub_one_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:43.93412+00:00
-- url     : https://prove2.me/submissions/e6e1ce5a-a789-4de5-80fb-73fb2f271ed1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqOneOfNormPowTwoPowSubOneLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormPowerTwoUnity
namespace GlobalTheory.NormPowerTwoUnity
theorem _root_.solution (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    rw [this]
    exact norm_sub_le _ _
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith
end GlobalTheory.NormPowerTwoUnity
