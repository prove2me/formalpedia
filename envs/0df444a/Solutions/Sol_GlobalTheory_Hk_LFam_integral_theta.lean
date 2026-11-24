-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.integral_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:10.946327+00:00
-- url     : https://prove2.me/submissions/7b2b63bf-7d1d-415d-b5d0-1388e1009edb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_tsum_exp_eq_integral
import Theorems.Thm_GlobalTheory_Hk_integral_integral_exp_kernel
import Theorems.Thm_GlobalTheory_Hk_LFam_summable_norm_aChi_exp
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_sum_aChi_sub_le

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
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (hχ : χ ≠ 1) :
    ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1 := by
  have hr : 𝓕.res χ = 0 := by unfold LFam.res; rw [if_neg hχ]
  have h0 : 𝓕.aChi χ 0 = 0 := by simp [LFam.aChi, 𝓕.a_zero]
  have hm : Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 𝓕.aChi χ n :=
    (measurable_from_top (f := fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, 𝓕.aChi χ n)).comp Nat.measurable_floor
  have h := integral_integral_exp_kernel _ hm (10 * 𝓕.B) (fun x hx => by
    have := 𝓕.norm_sum_aChi_sub_le χ hx.le
    rwa [hr, zero_mul, sub_zero] at this)
  unfold LFam.F LFam.mel
  rw [if_neg hχ, one_mul]
  simp only [hr, zero_mul, sub_zero]
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact tsum_exp_eq_integral _ h0 ht (𝓕.summable_norm_aChi_exp χ ht)
end LFam
end GlobalTheory.Hk
