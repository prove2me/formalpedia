-- Prove2me | solution 1 for LanglandsTunnell.exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12570cdd-7898-5270-ba7a-ea00f59b50a8

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Theorems.Thm_LanglandsTunnell_principal_profile_exists_ne_zero
import Theorems.Thm_LanglandsTunnell_norm_mulConvGaussian_le_rpow_max_mul_exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Theorems.Thm_LanglandsTunnell_mellin_mulConvGaussian_eq_archFactor_principal
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Theorems.Thm_LanglandsTunnell_principal_profile_sum_solves_whittaker_ode_weightOne
import Theorems.Thm_LanglandsTunnell_lowering_principal_profile_sum_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne

set_option autoImplicit false

open scoped Real

open MeasureTheory Set LanglandsTunnell

noncomputable section

namespace WhittakerWeightOneUniqueness

private noncomputable def prof (u₁ u₂ : ℂ) (b₁ b₂ : ZMod 2) (y : ℝ) : ℂ :=
  (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
    ((t : ℂ) ^ (u₁ + signShift b₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
      (((y / t : ℝ) : ℂ) ^ (u₂ + signShift b₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)

private noncomputable def wsum (u₁ u₂ : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y + (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y

private noncomputable def wdiff (u₁ u₂ : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y - (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y

private theorem norm_cpow_mul_prof_le (u₁ u₂ : ℂ) (b₁ b₂ : ZMod 2) :
    ∃ C N : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → ‖(y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ b₁ b₂ y‖ ≤ C * y ^ N := by
  obtain ⟨C, hC⟩ := norm_mulConvGaussian_le_rpow_max_mul_exp u₁ b₁ u₂ b₂
  refine ⟨max C 0, (1 / 2 - (u₁ + u₂) / 2).re + max (u₁ + signShift b₁).re (u₂ + signShift b₂).re, le_max_right _ _,
    fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
  have hexp : Real.exp (-(π * y)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
  have hM : 0 ≤ y ^ (max (u₁ + signShift b₁).re (u₂ + signShift b₂).re) := Real.rpow_nonneg hy0.le _
  have hP' : ‖prof u₁ u₂ b₁ b₂ y‖ ≤ max C 0 * y ^ (max (u₁ + signShift b₁).re (u₂ + signShift b₂).re) := by
    calc ‖prof u₁ u₂ b₁ b₂ y‖
          ≤ C * y ^ (max (u₁ + signShift b₁).re (u₂ + signShift b₂).re) * Real.exp (-(π * y)) := hC y hy
      _ ≤ max C 0 * y ^ (max (u₁ + signShift b₁).re (u₂ + signShift b₂).re) * Real.exp (-(π * y)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hM) (Real.exp_pos _).le
      _ ≤ max C 0 * y ^ (max (u₁ + signShift b₁).re (u₂ + signShift b₂).re) * 1 :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (le_max_right _ _) hM)
      _ = _ := mul_one _
  calc ‖(y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ b₁ b₂ y‖
        = ‖(y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2)‖ * ‖prof u₁ u₂ b₁ b₂ y‖ := norm_mul _ _
    _ = y ^ (1 / 2 - (u₁ + u₂) / 2).re * ‖prof u₁ u₂ b₁ b₂ y‖ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    _ ≤ y ^ (1 / 2 - (u₁ + u₂) / 2).re * (max C 0 * y ^ (max (u₁ + signShift b₁).re (u₂ + signShift b₂).re)) := by
        gcongr
    _ = max C 0 * y ^ ((1 / 2 - (u₁ + u₂) / 2).re + max (u₁ + signShift b₁).re (u₂ + signShift b₂).re) := by
        rw [Real.rpow_add hy0]
        ring

private theorem exists_eq_const_mul_wsum (u₁ u₂ : ℂ) (hu : u₁ ≠ u₂) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f y ≠ 0) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ y : ℝ, 0 < y → f y = A * wsum u₁ u₂ y := by

  obtain ⟨hFd, hFd', hFeq⟩ := principal_profile_sum_solves_whittaker_ode_weightOne u₁ u₂ ((u₁ + u₂) / 2)
    ((u₁ - u₂) / 2) rfl rfl 1 rfl (wsum u₁ u₂) (fun y => rfl)

  have hFgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖wsum u₁ u₂ y‖ ≤ C * y ^ N := by
    obtain ⟨C₁, N₁, hC₁, h₁⟩ := norm_cpow_mul_prof_le u₁ u₂ 1 0
    obtain ⟨C₂, N₂, hC₂, h₂⟩ := norm_cpow_mul_prof_le u₁ u₂ 0 1
    refine ⟨C₁ + C₂, max N₁ N₂, fun y hy => ?_⟩
    have hN₁ : y ^ N₁ ≤ y ^ max N₁ N₂ := Real.rpow_le_rpow_of_exponent_le hy (le_max_left _ _)
    have hN₂ : y ^ N₂ ≤ y ^ max N₁ N₂ := Real.rpow_le_rpow_of_exponent_le hy (le_max_right _ _)
    calc ‖wsum u₁ u₂ y‖ ≤ ‖(y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y‖
          + ‖(y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y‖ := norm_add_le _ _
      _ ≤ C₁ * y ^ N₁ + C₂ * y ^ N₂ := add_le_add (h₁ y hy) (h₂ y hy)
      _ ≤ C₁ * y ^ max N₁ N₂ + C₂ * y ^ max N₁ N₂ :=
          add_le_add (mul_le_mul_of_nonneg_left hN₁ hC₁) (mul_le_mul_of_nonneg_left hN₂ hC₂)
      _ = (C₁ + C₂) * y ^ max N₁ N₂ := by ring

  have hFne : ∃ y : ℝ, 0 < y ∧ wsum u₁ u₂ y ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨y₀, hy₀, hPy₀⟩ := principal_profile_exists_ne_zero u₁ 1 u₂ 0 ((u₁ + u₂) / 2)
      (fun y => (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y) (fun y => rfl)
    have hzero : ∀ y : ℝ, 0 < y → wsum u₁ u₂ y = 0 := fun y hy => hall y hy

    have hder : deriv (wsum u₁ u₂) y₀ = 0 := by
      have hev : wsum u₁ u₂ =ᶠ[nhds y₀] fun _ => (0 : ℂ) :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy₀) fun x hx => hzero x hx
      rw [hev.deriv_eq, deriv_const]
    have hlow := lowering_principal_profile_sum_eq u₁ u₂ ((u₁ + u₂) / 2) rfl (wsum u₁ u₂) (fun y => rfl) y₀ hy₀
    rw [hder, hzero y₀ hy₀, mul_zero, mul_zero, zero_add] at hlow

    have hsum0 : (y₀ : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y₀
        + (y₀ : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y₀ = 0 := hzero y₀ hy₀
    have hdiff0 : (y₀ : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y₀
        - (y₀ : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y₀ = 0 :=
      (mul_eq_zero.1 hlow.symm).resolve_left (sub_ne_zero.2 hu)
    apply hPy₀
    show (y₀ : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y₀ = 0
    linear_combination (hsum0 - hdiff0) / 2

  have hfeq : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
        + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * ((1 : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
          * f y = 0 := by
    intro y hy
    have e : (2 : ℂ) * (π : ℂ) * ((1 : ℝ) : ℂ) * (y : ℂ) - 2 * (π : ℂ) * (y : ℂ) = 0 := by push_cast; ring
    linear_combination hode y hy + f y * e
  obtain ⟨c₁, c₂, hcne, hlin⟩ :=
    linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ((u₁ - u₂) / 2) 1 f (wsum u₁ u₂) hf hf' hfeq
      hgr hFd hFd' hFeq hFgr
  obtain ⟨y₀, hy₀, hFy₀⟩ := hFne
  have hc₁ : c₁ ≠ 0 := by
    intro h0
    have hc₂ : c₂ ≠ 0 := by
      intro h2
      exact hcne (by rw [h0, h2]; rfl)
    have := hlin y₀ hy₀
    rw [h0, zero_mul, zero_add] at this
    exact hFy₀ ((mul_eq_zero.1 this).resolve_left hc₂)
  obtain ⟨y₁, hy₁, hfy₁⟩ := hne
  refine ⟨-c₂ / c₁, ?_, fun y hy => ?_⟩
  · intro hA
    have h := hlin y₁ hy₁
    have hc₂ : c₂ = 0 := by
      rcases div_eq_zero_iff.1 hA with h1 | h1
      · exact neg_eq_zero.1 h1
      · exact absurd h1 hc₁
    rw [hc₂, zero_mul, add_zero] at h
    exact hfy₁ ((mul_eq_zero.1 h).resolve_left hc₁)
  · have h := hlin y hy
    rw [div_mul_eq_mul_div, eq_div_iff hc₁]
    linear_combination h

end WhittakerWeightOneUniqueness

namespace WhittakerWeightOneMellin

private noncomputable def prof (u₁ u₂ : ℂ) (b₁ b₂ : ZMod 2) (y : ℝ) : ℂ :=
  (4 : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
    ((t : ℂ) ^ (u₁ + signShift b₁) * (Real.exp (-(π * t ^ 2)) : ℂ)) *
      (((y / t : ℝ) : ℂ) ^ (u₂ + signShift b₂) * (Real.exp (-(π * (y / t) ^ 2)) : ℂ)) / (t : ℂ)

private noncomputable def wsum (u₁ u₂ : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y + (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y

private noncomputable def wdiff (u₁ u₂ : ℂ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 y - (y : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 y

private theorem zmod_two_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  revert b
  decide

private theorem zmod_two_ne_cases (a₁ a₂ : ZMod 2) (h : a₁ ≠ a₂) : (a₁ = 1 ∧ a₂ = 0) ∨ (a₁ = 0 ∧ a₂ = 1) := by
  revert a₁ a₂
  decide

private theorem val_one_two : (1 : ZMod 2).val = 1 := rfl

private theorem one_add_one_two : (1 : ZMod 2) + 1 = 0 := by decide

private theorem signShift_re_nonneg (b : ZMod 2) : 0 ≤ (signShift b).re := by
  rcases zmod_two_cases b with rfl | rfl <;> simp

private theorem twist_principal (u₁ u₂ : ℂ) (b₁ b₂ b : ZMod 2) :
    (RealArchParam.principal u₁ b₁ u₂ b₂).twist 0 b = RealArchParam.principal u₁ (b₁ + b) u₂ (b₂ + b) := by
  simp [RealArchParam.twist]

private theorem archFactor_principal_ne_zero (v₁ v₂ : ℂ) (b₁ b₂ : ZMod 2) (s : ℂ)
    (h₁ : 0 < (s + (v₁ + signShift b₁)).re) (h₂ : 0 < (s + (v₂ + signShift b₂)).re) :
    (RealArchParam.principal v₁ b₁ v₂ b₂).archFactor s ≠ 0 := by
  simp [RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC,
    Complex.Gammaℝ_ne_zero_of_re_pos h₁, Complex.Gammaℝ_ne_zero_of_re_pos h₂]

private theorem sqrt_cpow (t : ℝ) (ht : 0 < t) (w : ℂ) :
    ((Real.sqrt t : ℝ) : ℂ) ^ w = (t : ℂ) ^ (w / 2) := by
  have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.2 ht
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hs.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 ht.ne'),
    ← Complex.ofReal_log hs.le, ← Complex.ofReal_log ht.le, Real.log_sqrt ht.le]
  congr 1
  push_cast
  ring

private theorem mellin_of_eq_prof (u₁ u₂ : ℂ) (b₁ b₂ : ZMod 2) (g : ℝ → ℂ) (s : ℂ) (h₁ : 0 < (s + u₁).re)
    (h₂ : 0 < (s + u₂).re)
    (hg : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) → (t : ℂ) ^ (s - 1) • g t = (t : ℂ) ^ (s - 1) • prof u₁ u₂ b₁ b₂ t) :
    MellinConvergent g s ∧ mellin g s = (RealArchParam.principal u₁ b₁ u₂ b₂).archFactor s := by
  have h₁' : 0 < (s + (u₁ + signShift b₁)).re := by
    have := signShift_re_nonneg b₁
    rw [Complex.add_re] at h₁
    rw [Complex.add_re, Complex.add_re]
    linarith
  have h₂' : 0 < (s + (u₂ + signShift b₂)).re := by
    have := signShift_re_nonneg b₂
    rw [Complex.add_re] at h₂
    rw [Complex.add_re, Complex.add_re]
    linarith
  have hval : mellin (prof u₁ u₂ b₁ b₂) s = (RealArchParam.principal u₁ b₁ u₂ b₂).archFactor s :=
    mellin_mulConvGaussian_eq_archFactor_principal u₁ b₁ u₂ b₂ s h₁' h₂'
  have hconvP : MellinConvergent (prof u₁ u₂ b₁ b₂) s := by
    by_contra hcv
    have h0 : mellin (prof u₁ u₂ b₁ b₂) s = 0 := integral_undef hcv
    rw [hval] at h0
    exact archFactor_principal_ne_zero u₁ u₂ b₁ b₂ s h₁' h₂' h0
  refine ⟨(integrableOn_congr_fun hg measurableSet_Ioi).2 hconvP, ?_⟩
  rw [← hval]
  simp only [mellin]
  exact setIntegral_congr_fun measurableSet_Ioi hg

private theorem mellin_symm (u₁ u₂ A ρ ε X : ℂ) (W : ℂ → ℂ) (b₁ b₂ : ZMod 2) (s : ℂ) (hρ : ρ * (2 * A) = 1)
    (hsel : (ε * X = 1 ∧ b₁ = 0 ∧ b₂ = 1) ∨ (ε * X = -1 ∧ b₁ = 1 ∧ b₂ = 0))
    (hW1 : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (A * wsum u₁ u₂ t))
    (hW2 : ∀ t : ℝ, 0 < t → W (-t) = ε * (((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (A * wdiff u₁ u₂ t)))
    (hs : max (-u₁.re) (-u₂.re) < s.re) :
    MellinConvergent (fun t : ℝ => (ρ * W t + X * (ρ * W (-t))) / (t : ℂ)) s ∧
      mellin (fun t : ℝ => (ρ * W t + X * (ρ * W (-t))) / (t : ℂ)) s
        = (RealArchParam.principal u₁ b₁ u₂ b₂).archFactor s := by
  have hm₁ := le_max_left (-u₁.re) (-u₂.re)
  have hm₂ := le_max_right (-u₁.re) (-u₂.re)
  have h₁ : 0 < (s + u₁).re := by rw [Complex.add_re]; linarith
  have h₂ : 0 < (s + u₂).re := by rw [Complex.add_re]; linarith
  apply mellin_of_eq_prof u₁ u₂ b₁ b₂ _ s h₁ h₂
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht'.ne'
  have hpow : (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) = (t : ℂ) := by
    rw [← Complex.cpow_add _ _ ht0]
    rw [show (u₁ + u₂ + 1) / 2 + (1 / 2 - (u₁ + u₂) / 2) = (1 : ℂ) by ring, Complex.cpow_one]
  congr 1
  rw [hW1 t ht', hW2 t ht', sqrt_cpow t ht', div_eq_iff ht0]
  simp only [wsum, wdiff]
  rcases hsel with ⟨hx, rfl, rfl⟩ | ⟨hx, rfl, rfl⟩
  · linear_combination
      (ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * A * (t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2)
          * (prof u₁ u₂ 0 1 t - prof u₁ u₂ 1 0 t)) * hx
        + ((t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 0 1 t) * hρ
        + prof u₁ u₂ 0 1 t * hpow
  · linear_combination
      (ρ * (t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * A * (t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2)
          * (prof u₁ u₂ 0 1 t - prof u₁ u₂ 1 0 t)) * hx
        + ((t : ℂ) ^ ((u₁ + u₂ + 1) / 2) * (t : ℂ) ^ (1 / 2 - (u₁ + u₂) / 2) * prof u₁ u₂ 1 0 t) * hρ
        + prof u₁ u₂ 1 0 t * hpow

private theorem exists_param_mellin (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (W : ℂ → ℂ) (f : ℝ → ℂ)
    (c : ℂ) (hc : c = u₁ - u₂ ∨ c = u₂ - u₁) (A ρ : ℂ) (hρ : ρ * (2 * A) = 1)
    (hprop : ∀ y : ℝ, 0 < y → f y = A * wsum u₁ u₂ y)
    (hWp : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f t)
    (hWm : ∀ t : ℝ, 0 < t →
      c * W (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (2 * (t : ℂ) * deriv f t + (4 * (π : ℂ) * (t : ℂ) - 1) * f t)) :
    ∃ P' : RealArchParam,
      (P' = RealArchParam.principal u₁ a₁ u₂ a₂ ∨ P' = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (b : ZMod 2) (s : ℂ), max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s
            = (P'.twist 0 b).archFactor s := by

  obtain ⟨hFd, -, -⟩ := principal_profile_sum_solves_whittaker_ode_weightOne u₁ u₂ ((u₁ + u₂) / 2)
    ((u₁ - u₂) / 2) rfl rfl 1 rfl (wsum u₁ u₂) (fun y => rfl)
  have hL : ∀ y : ℝ, 0 < y →
      2 * (y : ℂ) * deriv (wsum u₁ u₂) y + (4 * (π : ℂ) * (y : ℂ) - 1) * wsum u₁ u₂ y
        = (u₁ - u₂) * wdiff u₁ u₂ y :=
    fun y hy => lowering_principal_profile_sum_eq u₁ u₂ ((u₁ + u₂) / 2) rfl (wsum u₁ u₂) (fun y => rfl) y hy

  have hderiv : ∀ t : ℝ, 0 < t → deriv f t = A * deriv (wsum u₁ u₂) t := by
    intro t ht
    have hev : f =ᶠ[nhds t] fun x : ℝ => A * wsum u₁ u₂ x :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun x hx => hprop x hx
    rw [hev.deriv_eq, deriv_const_mul A (hFd.differentiableAt (Ioi_mem_nhds ht))]
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hρ
    exact zero_ne_one hρ

  have hW1 : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (A * wsum u₁ u₂ t) :=
    fun t ht => by rw [hWp t ht, hprop t ht]
  rcases hc with rfl | rfl
  ·
    have hW2 : ∀ t : ℝ, 0 < t →
        W (-t) = 1 * (((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (A * wdiff u₁ u₂ t)) := by
      intro t ht
      apply mul_left_cancel₀ (sub_ne_zero.2 hu)
      rw [hWm t ht, hderiv t ht, hprop t ht]
      linear_combination ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * A * hL t ht
    refine ⟨RealArchParam.principal u₁ 0 u₂ 1, ?_, ρ, hρ0, ?_⟩
    · rcases zmod_two_ne_cases a₁ a₂ ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro b s hs
      rcases zmod_two_cases b with rfl | rfl
      · rw [twist_principal]
        simp only [ZMod.val_zero, pow_zero, add_zero]
        exact mellin_symm u₁ u₂ A ρ 1 1 W 0 1 s hρ (Or.inl ⟨by norm_num, rfl, rfl⟩) hW1 hW2 hs
      · rw [twist_principal]
        simp only [val_one_two, pow_one, one_add_one_two, zero_add]
        exact mellin_symm u₁ u₂ A ρ 1 (-1) W 1 0 s hρ (Or.inr ⟨by norm_num, rfl, rfl⟩) hW1 hW2 hs
  ·
    have hW2 : ∀ t : ℝ, 0 < t →
        W (-t) = -1 * (((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * (A * wdiff u₁ u₂ t)) := by
      intro t ht
      apply mul_left_cancel₀ (sub_ne_zero.2 hu.symm)
      rw [hWm t ht, hderiv t ht, hprop t ht]
      linear_combination ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * A * hL t ht
    refine ⟨RealArchParam.principal u₁ 1 u₂ 0, ?_, ρ, hρ0, ?_⟩
    · rcases zmod_two_ne_cases a₁ a₂ ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro b s hs
      rcases zmod_two_cases b with rfl | rfl
      · rw [twist_principal]
        simp only [ZMod.val_zero, pow_zero, add_zero]
        exact mellin_symm u₁ u₂ A ρ (-1) 1 W 1 0 s hρ (Or.inr ⟨by norm_num, rfl, rfl⟩) hW1 hW2 hs
      · rw [twist_principal]
        simp only [val_one_two, pow_one, one_add_one_two, zero_add]
        exact mellin_symm u₁ u₂ A ρ (-1) (-1) W 0 1 s hρ (Or.inl ⟨by norm_num, rfl, rfl⟩) hW1 hW2 hs

end WhittakerWeightOneMellin

end

open WhittakerWeightOneUniqueness WhittakerWeightOneMellin in

theorem solution (u₁ u₂ : ℂ)
    (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (W : ℂ → ℂ) (f : ℝ → ℂ) (c : ℂ)
    (hc : c = u₁ - u₂ ∨ c = u₂ - u₁)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv f) y
          + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (π : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hne : ∃ y : ℝ, 0 < y ∧ f y ≠ 0)
    (hWp : ∀ t : ℝ, 0 < t → W t = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f t)
    (hWm : ∀ t : ℝ, 0 < t →
      c * W (-t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
        * (2 * (t : ℂ) * deriv f t + (4 * (π : ℂ) * (t : ℂ) - 1) * f t)) :
    ∃ P' : RealArchParam,
      (P' = RealArchParam.principal u₁ a₁ u₂ a₂ ∨ P' = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (b : ZMod 2) (s : ℂ), max (-u₁.re) (-u₂.re) < s.re →
        MellinConvergent (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (ρ * W t + (-1 : ℂ) ^ b.val * (ρ * W (-t))) / (t : ℂ)) s
            = (P'.twist 0 b).archFactor s := by
  obtain ⟨A, hA, hprop⟩ := exists_eq_const_mul_wsum u₁ u₂ hu f hf hf' hode hgr hne
  have h2A : (2 : ℂ) * A ≠ 0 := mul_ne_zero two_ne_zero hA
  have hρ : 1 / (2 * A) * (2 * A) = 1 := one_div_mul_cancel h2A
  exact exists_param_mellin u₁ u₂ a₁ a₂ ha hu W f c hc A (1 / (2 * A)) hρ hprop hWp hWm

end S_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
end P2MW
export P2MW.S_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne (solution)
