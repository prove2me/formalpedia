-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.norm_theta_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:30:42.428878+00:00
-- url     : https://prove2.me/submissions/0679478e-7ef7-4b2b-8592-8743d6d3154b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_LFam_a_le_mul
import Theorems.Thm_GlobalTheory_Hk_summable_nat_mul_exp_neg
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
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ 𝓕.B ^ 11 * t := by
  have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
  have hs : ∀ g, Summable (fun n : ℕ => 𝓕.a g n * Real.exp (-(t * n))) := fun g => by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (𝓕.a_nonneg g n) (Real.exp_pos _).le) (fun n => ?_)
      ((summable_nat_mul_exp_neg ht).mul_left 14)
    rw [← mul_assoc]
    gcongr
    exact 𝓕.a_le_mul g n
  have h1 : HasSum (fun n : ℕ => ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ))
      (∑ g, χ g * ((∑' n : ℕ, 𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ)) :=
    hasSum_sum fun g _ => (Complex.hasSum_ofReal.2 (hs g).hasSum).mul_left _
  have h2 : ∀ n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) =
      ∑ g, χ g * ((𝓕.a g n * Real.exp (-(t * n)) : ℝ) : ℂ) := fun n => by
    unfold LFam.aChi
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Complex.ofReal_mul, mul_assoc]
  simp only [h2]
  rw [h1.tsum_eq, 𝓕.res_eq_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ g : 𝓕.G, 𝓕.B ^ 10 * t := by
        refine norm_sum_le_of_le _ fun g _ => ?_
        rw [mul_div_assoc, ← mul_sub, norm_mul, 𝓕.norm_chi, one_mul, ← Complex.ofReal_div,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact 𝓕.theta g t ht ht1
    _ = Fintype.card 𝓕.G * (𝓕.B ^ 10 * t) := by simp
    _ ≤ 𝓕.B * (𝓕.B ^ 10 * t) := by gcongr; exact 𝓕.card_le
    _ = _ := by ring
end LFam
end GlobalTheory.Hk
