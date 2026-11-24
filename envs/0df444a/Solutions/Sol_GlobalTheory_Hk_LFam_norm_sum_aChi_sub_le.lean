-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.norm_sum_aChi_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:30:40.28904+00:00
-- url     : https://prove2.me/submissions/68fe0992-7ed8-4f4f-8e1a-b99085b7c683

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_chi
import Theorems.Thm_GlobalTheory_Hk_LFam_res_eq_sum

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
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n - 𝓕.res χ * x‖ ≤ 10 * 𝓕.B * Real.sqrt x := by
  unfold LFam.aChi
  rw [Finset.sum_comm, 𝓕.res_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ g : 𝓕.G, 10 * Real.sqrt x := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [← Finset.mul_sum, mul_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_sum,
          ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact 𝓕.count g x hx
    _ = Fintype.card 𝓕.G * (10 * Real.sqrt x) := by simp
    _ ≤ 𝓕.B * (10 * Real.sqrt x) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring
end LFam
end GlobalTheory.Hk
