-- Prove2me | solution 1 for MeasureTheory.norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4ed77f1e-1af7-59d3-a0ca-fe3e6e969596

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

namespace Ws31
namespace C1cB

noncomputable def osc (l : ℝ) (u : ℝ) : ℂ := Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))

theorem norm_osc (l u : ℝ) : ‖osc l u‖ = 1 := by
  unfold osc
  rw [Complex.norm_exp]
  simp

theorem continuous_osc (l : ℝ) : Continuous (osc l) := by
  unfold osc; fun_prop

theorem hasDerivAt_osc (l u : ℝ) :
    HasDerivAt (osc l) (Complex.I * (l : ℂ) * osc l u) u := by
  have h1 : HasDerivAt (fun y : ℝ => ((id y : ℝ) : ℂ)) ((1 : ℝ) : ℂ) u := (hasDerivAt_id u).ofReal_comp
  have h2 := (h1.const_mul (Complex.I * (l : ℂ))).cexp
  refine (h2.congr_deriv ?_)
  simp only [id, Complex.ofReal_one, mul_one, osc]
  ring

theorem tendsto_atTop_zero_of_hasCompactSupport (f : ℝ → ℂ) (hf : HasCompactSupport f) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  obtain ⟨R, hR⟩ := hf.isCompact.bddAbove
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop R] with x hx
  exact (image_eq_zero_of_notMem_tsupport (fun h => (not_le.mpr hx) (hR h))).symm

theorem tendsto_atBot_zero_of_hasCompactSupport (f : ℝ → ℂ) (hf : HasCompactSupport f) :
    Filter.Tendsto f Filter.atBot (nhds 0) := by
  obtain ⟨R, hR⟩ := hf.isCompact.bddBelow
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_lt_atBot R] with x hx
  exact (image_eq_zero_of_notMem_tsupport (fun h => (not_le.mpr hx) (hR h))).symm

theorem ibp_step (l : ℝ) (G : ℝ → ℂ) (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) :
    Complex.I * (l : ℂ) * ∫ u : ℝ, G u * osc l u = - ∫ u : ℝ, deriv G u * osc l u := by
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hGcont : Continuous G := hG.continuous
  have hu : ∀ x ∈ tsupport (osc l), HasDerivAt G (deriv G x) x := fun x _ => (hGd x).hasDerivAt
  have hv : ∀ x ∈ tsupport G, HasDerivAt (osc l) (Complex.I * (l : ℂ) * osc l x) x :=
    fun x _ => hasDerivAt_osc l x
  have i1 : Integrable (G * fun x => Complex.I * (l : ℂ) * osc l x) :=
    (hGcont.mul (continuous_const.mul (continuous_osc l))).integrable_of_hasCompactSupport hGc.mul_right
  have i2 : Integrable (deriv G * osc l) :=
    (hG'c.mul (continuous_osc l)).integrable_of_hasCompactSupport hGc.deriv.mul_right
  have hGo : HasCompactSupport (G * osc l) := hGc.mul_right
  have key := integral_mul_deriv_eq_deriv_mul hu hv i1 i2
    (tendsto_atBot_zero_of_hasCompactSupport _ hGo) (tendsto_atTop_zero_of_hasCompactSupport _ hGo)

  calc Complex.I * (l : ℂ) * ∫ u : ℝ, G u * osc l u
      = ∫ u : ℝ, Complex.I * (l : ℂ) * (G u * osc l u) := (integral_const_mul _ _).symm
    _ = ∫ u : ℝ, G u * (Complex.I * (l : ℂ) * osc l u) :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = 0 - 0 - ∫ u : ℝ, deriv G u * osc l u := key
    _ = - ∫ u : ℝ, deriv G u * osc l u := by ring

theorem ibp_iter (l : ℝ) : ∀ (n : ℕ) (G : ℝ → ℂ), ContDiff ℝ n G → HasCompactSupport G →
    (Complex.I * (l : ℂ)) ^ n * ∫ u : ℝ, G u * osc l u = (-1) ^ n * ∫ u : ℝ, iteratedDeriv n G u * osc l u := by
  intro n
  induction n with
  | zero => intro G _ _; simp [iteratedDeriv_zero]
  | succ n ih =>
    intro G hG hGc
    have hG' : ContDiff ℝ ((n : WithTop ℕ∞) + 1) G := by simpa using hG
    have h1 : ContDiff ℝ 1 G := hG'.of_le (by simp)
    have hdG : ContDiff ℝ n (deriv G) := (contDiff_succ_iff_deriv.mp hG').2.2
    have step := ibp_step l G h1 hGc
    have rec_ := ih (deriv G) hdG hGc.deriv
    rw [iteratedDeriv_succ', pow_succ, pow_succ]
    calc (Complex.I * (l : ℂ)) ^ n * (Complex.I * (l : ℂ)) * ∫ u : ℝ, G u * osc l u
        = (Complex.I * (l : ℂ)) ^ n * ((Complex.I * (l : ℂ)) * ∫ u : ℝ, G u * osc l u) := by ring
      _ = (Complex.I * (l : ℂ)) ^ n * (- ∫ u : ℝ, deriv G u * osc l u) := by rw [step]
      _ = - ((Complex.I * (l : ℂ)) ^ n * ∫ u : ℝ, deriv G u * osc l u) := by ring
      _ = - ((-1) ^ n * ∫ u : ℝ, iteratedDeriv n (deriv G) u * osc l u) := by rw [rec_]
      _ = (-1) ^ n * (-1) * ∫ u : ℝ, iteratedDeriv n (deriv G) u * osc l u := by ring

theorem norm_integral_mul_osc_le (l : ℝ) (G : ℝ → ℂ) :
    ‖∫ u : ℝ, G u * osc l u‖ ≤ ∫ u : ℝ, ‖G u‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show ‖G u * osc l u‖ = ‖G u‖
  rw [norm_mul, norm_osc, mul_one]

theorem main (N : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ N H) (hHc : HasCompactSupport H) (l : ℝ) :
    ‖∫ u : ℝ, H u * Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))‖
      ≤ 2 ^ N * ((∫ u : ℝ, ‖H u‖) + ∫ u : ℝ, ‖iteratedDeriv N H u‖) * (1 + |l|) ^ (-(N : ℝ)) := by
  change ‖∫ u : ℝ, H u * osc l u‖ ≤ _
  set A : ℝ := ∫ u : ℝ, ‖H u‖ with hA
  set B : ℝ := ∫ u : ℝ, ‖iteratedDeriv N H u‖ with hB
  have hA0 : 0 ≤ A := integral_nonneg fun u => norm_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun u => norm_nonneg _
  have hl0 : 0 < 1 + |l| := by positivity
  have hpow : (1 + |l|) ^ (-(N : ℝ)) = ((1 + |l|) ^ N)⁻¹ := by
    rw [Real.rpow_neg hl0.le, Real.rpow_natCast]
  rw [hpow]
  by_cases hl : |l| ≤ 1
  ·
    have h1 : ‖∫ u : ℝ, H u * osc l u‖ ≤ A := norm_integral_mul_osc_le l H
    have h2 : (1 + |l|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ hl0.le (by linarith) N
    have h3 : 1 ≤ 2 ^ N * ((1 + |l|) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div (pow_pos hl0 N)]; exact h2
    calc ‖∫ u : ℝ, H u * osc l u‖ ≤ A := h1
      _ ≤ (A + B) * 1 := by linarith
      _ ≤ (A + B) * (2 ^ N * ((1 + |l|) ^ N)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (add_nonneg hA0 hB0)
      _ = 2 ^ N * (A + B) * ((1 + |l|) ^ N)⁻¹ := by ring
  ·
    have hl1 : 1 < |l| := lt_of_not_ge hl
    have hlpos : 0 < |l| := lt_trans one_pos hl1
    have hne : (Complex.I * (l : ℂ)) ^ N ≠ 0 := by
      apply pow_ne_zero
      apply mul_ne_zero Complex.I_ne_zero
      exact_mod_cast (abs_pos.mp hlpos).symm.symm
    have hid := ibp_iter l N H hH hHc
    have hnI : ‖(Complex.I * (l : ℂ)) ^ N‖ = |l| ^ N := by
      rw [norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |l| ^ N * ‖∫ u : ℝ, H u * osc l u‖ ≤ B := by
      have := congrArg (fun z => ‖z‖) hid
      simp only [norm_mul, hnI, norm_pow, norm_neg, norm_one, one_pow, one_mul] at this
      rw [this]
      exact norm_integral_mul_osc_le l _
    have hlN : 0 < |l| ^ N := pow_pos hlpos N
    have h2 : ‖∫ u : ℝ, H u * osc l u‖ ≤ B * (|l| ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hlN, mul_comm]; exact h1

    have h3 : (|l| ^ N)⁻¹ ≤ 2 ^ N * ((1 + |l|) ^ N)⁻¹ := by
      have key : (1 + |l|) ^ N ≤ 2 ^ N * |l| ^ N := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hl0.le (by linarith) N
      have h2N : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero N two_ne_zero
      calc (|l| ^ N)⁻¹ = 2 ^ N * (2 ^ N * |l| ^ N)⁻¹ := by
            rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h2N, one_mul]
        _ ≤ 2 ^ N * ((1 + |l|) ^ N)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hl0 N) key) (pow_nonneg zero_le_two N)
    calc ‖∫ u : ℝ, H u * osc l u‖ ≤ B * (|l| ^ N)⁻¹ := h2
      _ ≤ (A + B) * (|l| ^ N)⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hlN.le)
      _ ≤ (A + B) * (2 ^ N * ((1 + |l|) ^ N)⁻¹) := mul_le_mul_of_nonneg_left h3 (add_nonneg hA0 hB0)
      _ = 2 ^ N * (A + B) * ((1 + |l|) ^ N)⁻¹ := by ring

end Ws31.C1cB

theorem solution
    (N : ℕ) (H : ℝ → ℂ) (hH : ContDiff ℝ N H) (hHc : HasCompactSupport H) (l : ℝ) :
    ‖∫ u : ℝ, H u * Complex.exp (Complex.I * (l : ℂ) * (u : ℂ))‖
      ≤ 2 ^ N * ((∫ u : ℝ, ‖H u‖) + ∫ u : ℝ, ‖iteratedDeriv N H u‖) * (1 + |l|) ^ (-(N : ℝ)) :=
  Ws31.C1cB.main N H hH hHc l

end S_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_norm_integral_mul_cexp_le_two_pow_mul_rpow_neg_of_contDiff_of_hasCompactSupport (solution)
