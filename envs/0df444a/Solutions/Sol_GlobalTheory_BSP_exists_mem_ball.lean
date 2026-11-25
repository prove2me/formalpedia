-- Prove2me | solution 1 for GlobalTheory.BSP.exists_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:21.803697+00:00
-- url     : https://prove2.me/submissions/337a5f59-7466-438a-b7c3-e355f5691a79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
namespace GlobalTheory.BSP
theorem _root_.solution (y : PreDisc l u ρ) : ∃ r : ℝ, 0 < r ∧ y ∈ ball l u ρ r := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : A) y
  refine ⟨(l : ℝ) ^ n + 1, by positivity, ?_⟩
  have e : y = a • (algebraMap A (PreDisc l u ρ) ((l : A) ^ 0 * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ n) := by
    rw [Algebra.smul_def, ← h, pow_zero, pow_zero, mul_one, map_one, one_mul, mul_assoc, ← mul_pow,
      IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 0, n, by simp, rfl⟩)
end GlobalTheory.BSP
