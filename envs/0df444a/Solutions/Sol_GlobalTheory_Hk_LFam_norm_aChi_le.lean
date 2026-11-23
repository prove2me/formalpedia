-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.norm_aChi_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:33.922574+00:00
-- url     : https://prove2.me/submissions/26c1b262-27de-4667-b414-5d3b6765a713

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_LFam_a_le_mul
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_chi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
namespace LFam
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.aChi χ n‖ ≤ 14 * 𝓕.B * n := by
  unfold LFam.aChi
  calc ‖∑ g, χ g * (𝓕.a g n : ℂ)‖ ≤ ∑ g : 𝓕.G, (14 * n : ℝ) := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [norm_mul, 𝓕.norm_chi, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.a_nonneg g n)]
        exact 𝓕.a_le_mul g n
    _ = Fintype.card 𝓕.G * (14 * n : ℝ) := by simp
    _ ≤ 𝓕.B * (14 * n : ℝ) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring
end LFam
end GlobalTheory.Hk
