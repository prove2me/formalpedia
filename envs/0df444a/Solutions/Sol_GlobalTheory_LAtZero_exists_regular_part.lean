-- Prove2me | solution 1 for GlobalTheory.LAtZero.exists_regular_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:07.997793+00:00
-- url     : https://prove2.me/submissions/659cca04-72c3-4959-85ee-0419309a5cf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivEqOrderDivAddAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionNearZero
import Theorems.Thm_GlobalTheory_LAtZero_norm_limit_le
import Theorems.Thm_GlobalTheory_logDeriv_eq_order_div_add_analytic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.LAtZero
namespace GlobalTheory.LAtZero
theorem _root_.solution (f e : ℂ → ℂ) (S : Set ℂ) (B : ℝ) (hS : S.Finite)
    (he : ContinuousAt e 0) (han : AnalyticAt ℂ f 0) (hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), f s = 0)
    (hS0 : f 0 = 0 → 0 ∈ S) (hSz : ∀ w ∈ S, f w = 0)
    (hT : ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| < 1 → f w = 0 → w ∈ S)
    (hbig : ∀ w ∈ S, w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖)
    (hcount : ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℝ) ≤ B)
    (hloc : ∀ s : ℝ, 0 < s → s < 1 → f s ≠ 0 →
      ‖deriv f s / f s + e s - ∑ᶠ w ∈ S, (analyticOrderNatAt f w : ℂ) / (s - w)‖ ≤ B) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv f s / f s = (analyticOrderNatAt f 0 : ℂ) / s + h s) ∧
      ‖h 0‖ ≤ 2 * B + ‖e 0‖ +
        ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0},
          ((analyticOrderNatAt f ρ : ℕ) : ℝ) / ‖ρ‖ := by
  classical
  obtain ⟨h, hh, hev⟩ := GlobalTheory.logDeriv_eq_order_div_add_analytic f 0 han hne
  simp only [sub_zero] at hev
  refine ⟨h, hh, hev.mono fun s hs => hs.2, ?_⟩
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS] at hcount hloc
  have key := norm_limit_le (fun s => deriv f s / f s) h e (fun s => f s ≠ 0) hS.toFinset
    (analyticOrderNatAt f) B hh.continuousAt he ?_ hev hloc
  swap
  · intro hz
    have : f 0 ≠ 0 := fun h0 => hz (by simpa using hS0 h0)
    rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr this]; rfl
  have hset : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ f ρ = 0} =
      ↑(hS.toFinset.filter fun ρ => 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨hT w a b c d, a, b, c⟩,
      fun ⟨d, a, b, c⟩ => ⟨a, b, c, hSz w d⟩⟩
  rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hsum : ‖∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)‖ ≤
      ∑ w ∈ hS.toFinset, ((analyticOrderNatAt f w : ℝ) +
        if 0 < w.re ∧ w.re < 1 ∧ |w.im| < 1 then (analyticOrderNatAt f w : ℝ) / ‖w‖ else 0) := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun w hw => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 0 _) fun w _ _ => ?_)
    · rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
      split_ifs with hc
      · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      · rw [add_zero]
        refine div_le_self (Nat.cast_nonneg _) ?_
        rcases le_or_gt w.re 0 with h1 | h1
        · exact hbig w (by simpa using Finset.mem_of_mem_erase hw) h1 (Finset.ne_of_mem_erase hw)
        rcases le_or_gt 1 w.re with h2 | h2
        · exact h2.trans (re_le_norm w)
        · have h3 : 1 ≤ |w.im| := not_lt.mp fun h3 => hc ⟨h1, h2, h3⟩
          exact h3.trans (abs_im_le_norm w)
    · split_ifs <;> positivity
  rw [Finset.sum_add_distrib] at hsum
  set X := ∑ w ∈ hS.toFinset.erase 0, (analyticOrderNatAt f w : ℂ) / (0 - w)
  have : ‖h 0‖ ≤ ‖h 0 + e 0 - X‖ + ‖e 0‖ + ‖X‖ := by
    calc ‖h 0‖ = ‖(h 0 + e 0 - X) - e 0 + X‖ := by congr 1; ring
      _ ≤ ‖(h 0 + e 0 - X) - e 0‖ + ‖X‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  linarith
end GlobalTheory.LAtZero
