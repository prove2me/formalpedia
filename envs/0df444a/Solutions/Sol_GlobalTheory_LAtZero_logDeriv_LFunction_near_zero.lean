-- Prove2me | solution 1 for GlobalTheory.LAtZero.logDeriv_LFunction_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:02:35.357633+00:00
-- url     : https://prove2.me/submissions/498d8f02-8920-44f5-8fe4-a096da7872a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivEqOrderDivAddAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionNearZero
import Theorems.Thm_GlobalTheory_LAtZero_exists_regular_part
import Theorems.Thm_GlobalTheory_LAtZero_norm_sub_two_le
import Theorems.Thm_GlobalTheory_LFunction_zero_of_re_nonpos
import Theorems.Thm_GlobalTheory_LWide_logDeriv_LFunction_strip
import Theorems.Thm_GlobalTheory_LogDerivZeros_main
import Theorems.Thm_GlobalTheory_ZetaWide_main


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∃ (m : ℕ) (h : ℂ → ℂ), m ≤ 1 ∧ AnalyticAt ℂ h 0 ∧ (∀ᶠ s in 𝓝[≠] (0 : ℂ), deriv (LFunction χ) s / LFunction χ s = (m : ℂ) / s + h s) ∧ ‖h 0‖ ≤ C * (Real.log (2 * N) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.ZetaWide.main
  refine ⟨2 * C₁ + 2 * C₂ + 2, by positivity, fun N _ χ hχ => ?_⟩
  have han : AnalyticAt ℂ (LFunction χ) 0 := by
    refine DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt) ?_
    exact isOpen_compl_singleton.mem_nhds (by simp)
  have hord : ∀ hL : LFunction χ 0 = 0, analyticOrderNatAt (LFunction χ) 0 = 1 := fun hL =>
    (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ 0 (by simp) hL).2.1
  have hm : analyticOrderNatAt (LFunction χ) 0 ≤ 1 := by
    by_cases hL : LFunction χ 0 = 0
    · exact (hord hL).le
    · rw [analyticOrderNatAt, han.analyticOrderAt_eq_zero.mpr hL]; simp
  have hne : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), LFunction χ s = 0 := by
    intro hz
    have h1 := hord hz.self_of_nhds
    rw [analyticOrderNatAt, analyticOrderAt_eq_top.mpr hz] at h1
    simp at h1
  have hbig : ∀ w : ℂ, LFunction χ w = 0 → w.re ≤ 0 → w ≠ 0 → 1 ≤ ‖w‖ := by
    intro w hw hre h0
    obtain ⟨n, rfl⟩ := (GlobalTheory.LFunction_zero_of_re_nonpos N χ hχ w hre hw).1
    rw [norm_neg, Complex.norm_natCast]
    have : n ≠ 0 := by rintro rfl; simp at h0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hL2 : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by simp)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog : 1 / 2 ≤ Real.log (2 * N) := by
    have h1 : Real.log 2 ≤ Real.log (2 * N) := Real.log_le_log (by norm_num) (by linarith)
    have := Real.log_two_gt_d9
    linarith
  have hnn : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  by_cases h1 : χ = 1
  · have hq : N = 1 := by
      rw [IsPrimitive, h1, conductor_one] at hχ
      exact hχ.symm
    subst hq
    have hf : LFunction χ = riemannZeta := LFunction_modOne_eq
    rw [hf] at han hm hne hbig hL2 hnn ⊢
    have A := H₂ 2 (by norm_num) (by simp) (by norm_num) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part riemannZeta (fun s => 1 / (s - 1)) _
      (C₂ * Real.log 2) A.1
      (ContinuousAt.div continuousAt_const (continuousAt_id.sub continuousAt_const) (by simp))
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), by simp, h⟩)
      (fun w hw => hw.2.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, by rintro rfl; simp at b, d⟩)
      (fun w hw => hbig w hw.2.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₂ s (by simp; linarith) (by simp; linarith)
          (by exact_mod_cast hs1.ne) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    simp only [Nat.cast_one, mul_one] at hlog ⊢
    have e1 : ‖(1 : ℂ) / (0 - 1)‖ = 1 := by simp
    rw [e1]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]
  · have A := H₁ N χ h1 2 (by norm_num) (by simp) hL2
    simp only [im_ofNat, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at A
    obtain ⟨h, ha, hb, hc⟩ := exists_regular_part (LFunction χ) (fun _ => 0) _
      (C₁ * Real.log (N * 2)) A.1 continuousAt_const
      han hne (fun h => ⟨norm_sub_two_le (by simp) (by simp) (by simp), h⟩)
      (fun w hw => hw.2)
      (fun w a b c d => ⟨norm_sub_two_le a.le b c, d⟩)
      (fun w hw => hbig w hw.2) A.2.1 (fun s hs0 hs1 hs => by
        have B := (H₁ N χ h1 s (by simp; linarith) (by simp; linarith) hs).2.2
        simpa only [ofReal_im, ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] using B)
    refine ⟨_, h, hm, ha, hb, hc.trans ?_⟩
    rw [norm_zero, mul_comm (N : ℝ) 2]
    nlinarith [mul_nonneg hC₁.le hnn, mul_nonneg hC₂.le hnn]
end GlobalTheory.LAtZero
