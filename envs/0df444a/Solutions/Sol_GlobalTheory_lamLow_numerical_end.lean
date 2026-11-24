-- Prove2me | solution 1 for GlobalTheory.lamLow_numerical_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:11.433536+00:00
-- url     : https://prove2.me/submissions/c3d64294-eb0e-4117-aad2-be4577adf6f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LamLowNumericalEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (f n r : ℕ) (L' dmax mass Lq lam : ℝ) (H dt dk dD : Fin f → ℝ), 8 ≤ n → 2 * r ≤ n → 1 ≤ r → 1 ≤ f → (5.5 : ℝ) ≤ L' → Real.log n ≤ L' → 0 ≤ dmax → Real.log (dmax + 2) ≤ 2 * L' → 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass → 0 < Lq → |Real.log Lq| ≤ f * r / 4 → (∀ ρ, 0 < H ρ ∧ 1 ≤ dt ρ ∧ 1 ≤ dk ρ ∧ 0 < dD ρ ∧ Real.log (dD ρ) ≤ 2 + (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2))) → lam = mass * Lq * ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) → ∑ ρ, Real.log (H ρ) - 2 * f * (n : ℝ) ^ 2 * L' ≤ Real.log lam := by
  intro f n r L' dmax mass Lq lam H dt dk dD hn hr hr1 hf hL' hlogn hdmax hlogd hmass hLq hlogLq hρ hlam
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hr2 : 2 * (r : ℝ) ≤ n := by exact_mod_cast hr
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hnpos : (0 : ℝ) < n := by linarith
  have hrpos : (0 : ℝ) < r := by linarith
  have hmpos : 0 < mass := lt_of_lt_of_le (by positivity) hmass
  have hlogmass : -((n : ℝ) * Real.log 2 + (n : ℝ) * Real.log n) ≤ Real.log mass := by
    have h1 := Real.log_le_log (by positivity) hmass
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have hfac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.factorial_le_pow n
    linarith
  have hX : Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 * L' := by
    have hd : (0 : ℝ) < dmax + 2 := by linarith
    have h3 : 3 * (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hle : 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 3 * (dmax + 2) := by
      calc 3 * (r : ℝ) ^ 2 * n * (dmax + 2) ≤ (n : ℝ) ^ 2 * n * (dmax + 2) := by gcongr
        _ = (n : ℝ) ^ 3 * (dmax + 2) := by ring
    have hpos : 0 < 3 * (r : ℝ) ^ 2 * n * (dmax + 2) :=
      mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hrpos 2)) hnpos) hd
    have h4 := Real.log_le_log hpos hle
    rw [Real.log_mul (pow_pos hnpos 3).ne' hd.ne', Real.log_pow] at h4
    push_cast at h4
    linarith
  have hsq : (r : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 / 4 := by nlinarith
  have hdD : (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ 5 / 4 * (n : ℝ) ^ 2 * L' := by
    calc (r : ℝ) ^ 2 * Real.log (3 * (r : ℝ) ^ 2 * n * (dmax + 2)) ≤ (r : ℝ) ^ 2 * (5 * L') :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (n : ℝ) ^ 2 / 4 * (5 * L') := mul_le_mul_of_nonneg_right hsq (by linarith)
      _ = 5 / 4 * (n : ℝ) ^ 2 * L' := by ring
  have hfac_pos : ∀ ρ, 0 < H ρ * dt ρ * dk ρ / dD ρ := fun ρ => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    exact div_pos (mul_pos (mul_pos h1 ht) hk) h4
  have hprodpos : 0 < ∏ ρ, (H ρ * dt ρ * dk ρ / dD ρ) := Finset.prod_pos (fun ρ _ => hfac_pos ρ)
  have e1 : Real.log lam = Real.log mass + Real.log Lq + ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    rw [hlam, Real.log_mul (mul_pos hmpos hLq).ne' hprodpos.ne', Real.log_mul hmpos.ne' hLq.ne',
      Real.log_prod (fun ρ _ => (hfac_pos ρ).ne')]
  have e2 : ∀ ρ, Real.log (H ρ) - (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤ Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    intro ρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hρ ρ
    have ht : 0 < dt ρ := by linarith
    have hk : 0 < dk ρ := by linarith
    rw [Real.log_div (mul_pos (mul_pos h1 ht) hk).ne' h4.ne', Real.log_mul (mul_pos h1 ht).ne' hk.ne',
      Real.log_mul h1.ne' ht.ne']
    have := Real.log_nonneg h2
    have := Real.log_nonneg h3
    linarith
  have hsum : ∑ ρ, Real.log (H ρ) - (f : ℝ) * (2 + 5 / 4 * (n : ℝ) ^ 2 * L') ≤
      ∑ ρ, Real.log (H ρ * dt ρ * dk ρ / dD ρ) := by
    have := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => e2 ρ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have hLqlow : -((f : ℝ) * r / 4) ≤ Real.log Lq := by
    have := neg_abs_le (Real.log Lq)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hfL : 1 ≤ (f : ℝ) * L' := by nlinarith
  have hP1 : (n : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hfL hnpos.le]
  have hnL : 0 ≤ (n : ℝ) * L' := by positivity
  have hP2 : (n : ℝ) * L' ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_right hf1 hnL]
  have hP3 : (f : ℝ) * r / 4 ≤ f * n * L' := by
    have hrn : (r : ℝ) / 4 ≤ n * L' := by nlinarith
    linarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0 : ℝ) ≤ f)]
  have hnL2 : (2 : ℝ) ≤ n * L' := by nlinarith [mul_le_mul hn8 hL' (by norm_num) hnpos.le]
  have hP4 : 2 * (f : ℝ) ≤ f * n * L' := by linarith [mul_le_mul_of_nonneg_left hnL2 (by linarith : (0 : ℝ) ≤ f)]
  have hbig : 8 * ((f : ℝ) * n * L') ≤ f * (n : ℝ) ^ 2 * L' := by
    have h0 : 0 ≤ (f : ℝ) * n * L' := by positivity
    linarith [mul_le_mul_of_nonneg_right hn8 h0]
  have hm1 := mul_le_mul_of_nonneg_left hlog2 hnpos.le
  have hm2 := mul_le_mul_of_nonneg_left hlogn hnpos.le
  rw [e1]
  linarith
end GlobalTheory
