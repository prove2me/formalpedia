-- Prove2me | solution 1 for GlobalTheory.LogDerivZeros.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:18.860407+00:00
-- url     : https://prove2.me/submissions/bdc5f1ed-fc86-48bc-b8f3-3304cebd3dbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Theorems.Thm_GlobalTheory_LogDerivZeros_exists_factor
import Theorems.Thm_GlobalTheory_LogDerivZeros_norm_logDeriv_le
import Theorems.Thm_GlobalTheory_LogDerivZeros_norm_le_of_sphere
import Theorems.Thm_GlobalTheory_LogDerivZeros_norm_one_sub_conj_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LogDerivZeros
namespace GlobalTheory.LogDerivZeros
theorem _root_.solution : ∀ r R : ℝ, 0 < r → r < R → R < 1 → ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (M : ℝ), AnalyticOnNhd ℂ f (Metric.closedBall 0 1) → f 0 ≠ 0 → (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ M) → ({w : ℂ | ‖w‖ ≤ R ∧ f w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}, (analyticOrderNatAt f w : ℝ)) ≤ C * (1 + Real.log (M / ‖f 0‖))) ∧ ∀ z : ℂ, ‖z‖ ≤ r → f z ≠ 0 → ‖deriv f z / f z - ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}, (analyticOrderNatAt f w : ℂ) / (z - w)‖ ≤ C * (1 + Real.log (M / ‖f 0‖)) := by
  intro r R hr hrR hR1
  have hR : 0 < R := hr.trans hrR
  have hc1 : 0 < -Real.log R := neg_pos.2 (Real.log_neg hR hR1)
  have hc2 : 0 < -Real.log (1 - R) := neg_pos.2 (Real.log_neg (by linarith) (by linarith))
  set c1 := -Real.log R with hc1d
  set c2 := -Real.log (1 - R) with hc2d
  have hRr : 0 < R - r := by linarith
  have hA : 0 < 8 * R / (R - r) ^ 2 := by positivity
  set A := 8 * R / (R - r) ^ 2 with hAd
  refine ⟨c1⁻¹ + A * (1 + c1⁻¹ * c2), by positivity, ?_⟩
  intro f M hf hf0 hM
  have h0m : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  have hf0' : 0 < ‖f 0‖ := norm_pos_iff.2 hf0
  have hM0 : ‖f 0‖ ≤ M := hM 0 h0m
  have hMp : 0 < M := hf0'.trans_le hM0
  have hL : 0 ≤ Real.log (M / ‖f 0‖) := Real.log_nonneg ((one_le_div hf0').2 hM0)
  set L := Real.log (M / ‖f 0‖) with hLd
  have hconn := (convex_closedBall (0 : ℂ) 1).isPreconnected
  have hfin : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}.Finite := by
    have h1 := hf.preimage_zero_mem_codiscreteWithin hf0 h0m ⟨⟨0, h0m⟩, hconn⟩
    refine ((isCompact_closedBall (0 : ℂ) 1).finite_sdiff_of_mem_codiscreteWithin h1).subset ?_
    rintro w ⟨hw, hw0⟩
    exact ⟨by simpa using hw.trans hR1.le, by simpa using hw0⟩
  set S := hfin.toFinset with hSd
  have hS : ∀ w, w ∈ S ↔ ‖w‖ ≤ R ∧ f w = 0 := fun w => by simp [hSd]
  have hSU : ∀ w ∈ S, w ∈ Metric.closedBall (0 : ℂ) 1 := fun w hw => by
    simpa using ((hS w).1 hw).1.trans hR1.le
  have ho : ∀ w ∈ S, analyticOrderAt f w ≠ ⊤ := fun w hw =>
    hf.analyticOrderAt_ne_top_of_isPreconnected hconn h0m (hSU w hw)
      (by rw [(hf 0 h0m).analyticOrderAt_eq_zero.2 hf0]; simp)
  obtain ⟨g, hg, hfg, hg0⟩ := exists_factor hf S hSU ho
  set m : ℂ → ℕ := analyticOrderNatAt f with hm
  set N : ℕ := ∑ w ∈ S, m w with hN
  have hnorm : ∀ z, ‖f z‖ = (∏ w ∈ S, ‖z - w‖ ^ m w) * ‖g z‖ := fun z => by
    rw [hfg z, norm_mul, norm_prod]; simp only [norm_pow]
  have hg00 : ‖f 0‖ ≤ R ^ N * ‖g 0‖ := by
    rw [hnorm 0, hN, ← Finset.prod_pow_eq_pow_sum]
    gcongr with w hw
    simpa using ((hS w).1 hw).1
  have hgM : ‖g 0‖ ≤ M := by
    have hh : AnalyticOnNhd ℂ (fun z => (∏ w ∈ S, (1 - (starRingEnd ℂ) w * z) ^ m w) * g z)
        (Metric.closedBall 0 1) := fun z hz => AnalyticAt.mul (by fun_prop) (hg z hz)
    have := norm_le_of_sphere hh (B := M) (z := 0) (fun z hz => by
      have h1 := hM z (by simpa using hz.le)
      rw [hnorm z] at h1
      rw [norm_mul, norm_prod]
      simpa only [norm_pow, norm_one_sub_conj_mul hz] using h1) (by simp)
    simpa using this
  have hNL : (N : ℝ) ≤ c1⁻¹ * L := by
    have h1 : ‖f 0‖ ≤ R ^ N * M := hg00.trans (by gcongr)
    have h2 := Real.log_le_log hf0' h1
    rw [Real.log_mul (by positivity) hMp.ne', Real.log_pow] at h2
    rw [← div_eq_inv_mul, le_div_iff₀ hc1, hLd, Real.log_div hMp.ne' hf0'.ne', hc1d]
    linarith
  have hRN : R ^ N ≤ 1 := pow_le_one₀ hR.le hR1.le
  have hg01 : ‖f 0‖ ≤ ‖g 0‖ := hg00.trans (mul_le_of_le_one_left (norm_nonneg _) hRN)
  have hgB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖g z‖ ≤ M / (1 - R) ^ N := fun z hz => by
    refine norm_le_of_sphere hg (fun u hu => ?_) hz
    have h1R : 0 < 1 - R := by linarith
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ (hM u (by simpa using hu.le))
    rw [hnorm u, hN, ← Finset.prod_pow_eq_pow_sum]
    gcongr with w hw
    have := ((hS w).1 hw).1
    have := norm_sub_norm_le u w
    linarith
  have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.closedBall 0 1 :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR1.le)
  have hgne : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0 := fun z hz h0 =>
    hg0 z ((hS z).2 ⟨(mem_ball_zero_iff.1 hz).le, by rw [hfg z, h0, mul_zero]⟩) h0
  have hK : 0 < 1 + L + N * c2 := by positivity
  have hgb : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖g z‖ ≤ ‖g 0‖ * Real.exp (1 + L + N * c2) := by
    intro z hz
    have h1R : 0 < 1 - R := by linarith
    refine (hgB z (by simpa using hsub hz)).trans ?_
    have e : M / (1 - R) ^ N = ‖f 0‖ * Real.exp (L + N * c2) := by
      rw [Real.exp_add, hLd, Real.exp_log (by positivity), hc2d, mul_neg, Real.exp_neg,
        ← Real.log_pow, Real.exp_log (by positivity)]
      field_simp
    rw [e]
    gcongr
    linarith
  have hset : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0} = (S : Set ℂ) := by simp [hSd]
  refine ⟨⟨hfin, ?_⟩, fun z hz hfz => ?_⟩
  · rw [hset, finsum_mem_coe_finset]
    have : (∑ w ∈ S, (m w : ℝ)) = N := by rw [hN]; push_cast; rfl
    rw [this]
    refine hNL.trans ?_
    have : 0 ≤ A * (1 + c1⁻¹ * c2) := by positivity
    gcongr <;> linarith
  · rw [hset, finsum_mem_coe_finset]
    have hzb : z ∈ Metric.ball (0 : ℂ) R := mem_ball_zero_iff.2 (hz.trans_lt hrR)
    have hzw : ∀ w ∈ S, z - w ≠ 0 := fun w hw h => hfz (by rw [sub_eq_zero.1 h]; exact ((hS w).1 hw).2)
    have hld : deriv f z / f z = ∑ w ∈ S, (m w : ℂ) / (z - w) + deriv g z / g z := by
      have e : f = fun z => (∏ w ∈ S, (z - w) ^ m w) * g z := funext hfg
      rw [← logDeriv_apply, ← logDeriv_apply]
      conv_lhs => rw [e]
      rw [logDeriv_mul (f := fun z => ∏ w ∈ S, (z - w) ^ m w) z
        (Finset.prod_ne_zero_iff.2 fun w hw => pow_ne_zero _ (hzw w hw)) (hgne z hzb)
        (by fun_prop) (hg z (hsub hzb)).differentiableAt]
      congr 1
      rw [logDeriv_prod (f := fun w z => (z - w) ^ m w) (fun w hw => pow_ne_zero _ (hzw w hw))
        (fun w hw => by fun_prop)]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply]
      simp [div_eq_mul_inv]
    rw [hld, add_sub_cancel_left]
    refine (norm_logDeriv_le hr hrR hK (hg.mono hsub).differentiableOn hgne hgb hz).trans ?_
    have h1 : 1 + L + N * c2 ≤ (1 + c1⁻¹ * c2) * (1 + L) := by
      have : N * c2 ≤ c1⁻¹ * L * c2 := by gcongr
      have : 0 ≤ c1⁻¹ * c2 := by positivity
      nlinarith
    have h2 : 0 ≤ c1⁻¹ * (1 + L) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hA.le
    rw [← hAd]
    nlinarith
end GlobalTheory.LogDerivZeros
