-- Prove2me | solution 1 for LanglandsTunnell.exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/a2a66e23-ac88-5ae9-80f5-aea391383d7f

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Group.Even
import Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing
import Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded

set_option autoImplicit false

open scoped Real

noncomputable section

namespace GammaP41

open Real Set

theorem bdd_Icc (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (a b : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Icc a b, ‖f y‖ ≤ M := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le ha hy.1
  have hcont : ContinuousOn f (Set.Icc a b) := (hf.continuousOn).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.exists_norm_le
  exact ⟨max M 0, le_max_right _ _, fun y hy => (hM _ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem extend_bound (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (L e C : ℝ) (he : 0 ≤ e)
    (hC : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ e) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ y : ℝ, 0 < y → y ≤ L → ‖f y‖ ≤ C' * y ^ e := by
  obtain ⟨M, hM0, hM⟩ := bdd_Icc f hf 1 L one_pos
  refine ⟨max C 0 + M, by positivity, fun y hy hyL => ?_⟩
  have hye : 0 ≤ y ^ e := (Real.rpow_pos_of_pos hy e).le
  rcases le_or_gt y 1 with h1 | h1
  · calc ‖f y‖ ≤ C * y ^ e := hC y hy h1
      _ ≤ max C 0 * y ^ e := by gcongr; exact le_max_left _ _
      _ ≤ (max C 0 + M) * y ^ e := by nlinarith
  · have h1e : 1 ≤ y ^ e := Real.one_le_rpow h1.le he
    calc ‖f y‖ ≤ M := hM y ⟨h1.le, hyL⟩
      _ ≤ M * y ^ e := le_mul_of_one_le_right hM0 h1e
      _ ≤ (max C 0 + M) * y ^ e := by nlinarith [le_max_right C 0]

theorem rpow_bound_mono {f : ℝ → ℂ} {C e e' : ℝ} (hee : e' ≤ e)
    (hC : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ e) :
    ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ max C 0 * y ^ e' := by
  intro y hy hy1
  calc ‖f y‖ ≤ C * y ^ e := hC y hy hy1
    _ ≤ max C 0 * y ^ e := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * y ^ e' := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hee) (le_max_right _ _)

theorem stepA (q : ℂ) (hq : q ≠ 0) (κ c : ℂ) (f fup fdn : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (Bup Bdn : ℝ) (hup : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖fup y‖ ≤ Bup) (hdn : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖fdn y‖ ≤ Bdn)
    (hrel : ∀ y : ℝ, 0 < y → 2 * q * ((y : ℂ) * deriv f y - f y) +
      8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * (κ * fup y + c * fdn y) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 - ε) := by
  set u : ℝ → ℂ := fun y => -(8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * (κ * fup y + c * fdn y)) / (2 * q) with hu
  have hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = 1 * f y + u y := by
    intro y hy
    have h := hrel y hy
    simp only [hu]
    field_simp
    linear_combination h
  set A : ℝ := 4 * Real.pi * (‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0) / ‖q‖ with hA
  have hub : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖u y‖ ≤ A * y ^ (1 : ℝ) := by
    intro y hy hy1
    rw [Real.rpow_one]
    have hq' : 0 < ‖q‖ := norm_pos_iff.mpr hq
    simp only [hu, norm_div, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hy]
    rw [div_le_iff₀ (by positivity), hA]
    have h1 : ‖κ * fup y + c * fdn y‖ ≤ ‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0 := by
      calc ‖κ * fup y + c * fdn y‖ ≤ ‖κ * fup y‖ + ‖c * fdn y‖ := norm_add_le _ _
        _ = ‖κ‖ * ‖fup y‖ + ‖c‖ * ‖fdn y‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0 := by
            gcongr
            · exact (hup y hy hy1).trans (le_max_left _ _)
            · exact (hdn y hy hy1).trans (le_max_left _ _)
    calc 8 * Real.pi * y * ‖κ * fup y + c * fdn y‖ ≤ 8 * Real.pi * y * (‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0) := by gcongr
      _ = 4 * Real.pi * (‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0) / ‖q‖ * y * (2 * ‖q‖) := by field_simp; ring
  obtain ⟨C, hC⟩ := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing 1 1 A f u hf hub hfeq ε hε
  refine ⟨C, fun y hy hy1 => ?_⟩
  have := hC y hy hy1
  simpa using this

theorem rpow_m32_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (-(3 / 2 : ℝ) * (y ^ (-(3 / 2 : ℝ)) * y⁻¹)) y := by
  have h := Real.hasDerivAt_rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hy.ne')
  rw [Real.rpow_sub_one hy.ne', div_eq_mul_inv] at h
  exact h

theorem rescale (κ lam : ℂ) (hκ : κ ≠ 0) (νC : ℂ) (hν : νC ^ 2 = 1 - 4 * lam) (F R : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - 3 * (y : ℂ) * deriv F y +
      (3 + 4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y = R y) :
    let c : ℝ := 2 * ‖κ‖
    let G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c)
    0 < c ∧ DifferentiableOn ℝ G (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv G) (Set.Ioi 0) ∧
    (∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv G) Y + (1 / 4 - νC ^ 2 - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * G Y =
        ((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * R (Y / c)) ∧
    (∀ y : ℝ, 0 < y → G (c * y) = (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F y) ∧
    (∀ y : ℝ, 0 < y → ((c * y : ℝ) : ℂ) * deriv G (c * y) + (1 / 2 : ℂ) * G (c * y) =
        (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * ((y : ℂ) * deriv F y - F y)) ∧
    (∀ y : ℝ, 0 < y → ((c * y : ℝ) : ℂ) * deriv G (c * y) + (3 / 2 : ℂ) * G (c * y) =
        (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * ((y : ℂ) * deriv F y)) := by
  intro c G
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun y => (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F y with hgdef
  set g1 : ℝ → ℂ := fun y => (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * (-(3 / 2 : ℂ) * (y : ℂ)⁻¹ * F y + deriv F y) with hg1def
  set g2 : ℝ → ℂ := fun y => (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) *
    ((15 / 4 : ℂ) * (y : ℂ)⁻¹ * (y : ℂ)⁻¹ * F y - 3 * (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) with hg2def
  have hFd : ∀ y : ℝ, 0 < y → HasDerivAt F (deriv F y) y :=
    fun y hy => (hF.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hFdd : ∀ y : ℝ, 0 < y → HasDerivAt (deriv F) (deriv (deriv F) y) y :=
    fun y hy => (hF'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hpwC : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (((x ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ))
      (((-(3 / 2 : ℝ) * (y ^ (-(3 / 2 : ℝ)) * y⁻¹)) : ℝ) : ℂ) y :=
    fun y hy => (rpow_m32_hasDerivAt hy).ofReal_comp
  have hg1 : ∀ y : ℝ, 0 < y → HasDerivAt g (g1 y) y := by
    intro y hy
    have h := (hpwC y hy).mul (hFd y hy)
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    convert h using 1 <;> try rfl
    simp only [hg1def]; push_cast; ring
  have hderiv_g : ∀ y : ℝ, 0 < y → deriv g y = g1 y := fun y hy => (hg1 y hy).deriv
  have hg2 : ∀ y : ℝ, 0 < y → HasDerivAt g1 (g2 y) y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hinv : HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
      have h1 := (hasDerivAt_inv hy.ne').ofReal_comp
      have hfun : (fun x : ℝ => (x : ℂ)⁻¹) = fun x : ℝ => (((x⁻¹ : ℝ)) : ℂ) := by funext x; push_cast; rfl
      rw [hfun]
      convert h1 using 1
      push_cast; ring
    have hin : HasDerivAt (fun x : ℝ => -(3 / 2 : ℂ) * (x : ℂ)⁻¹ * F x + deriv F x)
        (-(3 / 2 : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * F y + -(3 / 2 : ℂ) * (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) y := by
      have := ((hinv.const_mul (-(3 / 2 : ℂ))).mul (hFd y hy)).add (hFdd y hy)
      convert this using 1 <;> first | rfl | ring
    have h := (hpwC y hy).mul hin
    convert h using 1 <;> try rfl
    simp only [hg2def]; push_cast; field_simp; ring
  have hg1d : ∀ y : ℝ, 0 < y → HasDerivAt (deriv g) (g2 y) y := by
    intro y hy
    refine (hg2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_g s hs
  have hGg : G = fun Y => g (Y / c) := rfl
  have hdiv : ∀ Y : ℝ, HasDerivAt (fun X : ℝ => X / c) (1 / c) Y := fun Y => by
    simpa using (hasDerivAt_id Y).div_const c
  have hG1 : ∀ Y : ℝ, 0 < Y → HasDerivAt G ((1 / c) • g1 (Y / c)) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    rw [hGg]; exact (hg1 _ hy).scomp Y (hdiv Y)
  have hderiv_G : ∀ Y : ℝ, 0 < Y → deriv G Y = (1 / c) • g1 (Y / c) := fun Y hY => (hG1 Y hY).deriv
  have hG2 : ∀ Y : ℝ, 0 < Y → HasDerivAt (deriv G) ((1 / c) • ((1 / c) • g2 (Y / c))) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    have h := ((hg2 _ hy).scomp Y (hdiv Y)).const_smul (1 / c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hY] with s hs
    rw [hderiv_G s hs]; rfl
  have hGd : DifferentiableOn ℝ G (Set.Ioi 0) := fun Y hY => (hG1 Y hY).differentiableAt.differentiableWithinAt
  have hGd' : DifferentiableOn ℝ (deriv G) (Set.Ioi 0) := fun Y hY => (hG2 Y hY).differentiableAt.differentiableWithinAt
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcn : (c : ℂ) ^ 2 = 4 * ((‖κ‖ : ℝ) : ℂ) ^ 2 := by show ((2 * ‖κ‖ : ℝ) : ℂ) ^ 2 = _; push_cast; ring
  have hsum : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * g2 y + (-(3 / 4 : ℂ) + 4 * lam - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y =
      (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * R y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := heq y hy
    have h2 : (y : ℂ) ^ 2 * g2 y = (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) *
        ((15 / 4 : ℂ) * F y - 3 * (y : ℂ) * deriv F y + (y : ℂ) ^ 2 * deriv (deriv F) y) := by
      simp only [hg2def]; field_simp
    rw [h2]
    simp only [hgdef]
    linear_combination (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * e +
      (-(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F y) * hcn
  refine ⟨hc, hGd, hGd', fun Y hY => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have hy : 0 < Y / c := div_pos hY hc
    rw [(hG2 Y hY).deriv]
    have hYy : (Y : ℂ) = (c : ℂ) * ((Y / c : ℝ) : ℂ) := by push_cast; field_simp
    have h3 : (Y : ℂ) ^ 2 * ((1 / c) • ((1 / c) • g2 (Y / c))) = (((Y / c : ℝ)) : ℂ) ^ 2 * g2 (Y / c) := by
      rw [hYy]; simp only [Complex.real_smul]; push_cast; field_simp
    have hGY : G Y = g (Y / c) := rfl
    rw [h3, hGY, hYy, hν]
    linear_combination hsum (Y / c) hy
  · show g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
  · rw [hderiv_G _ (by positivity)]
    show ((c * y : ℝ) : ℂ) * ((1 / c) • g1 (c * y / c)) + (1 / 2 : ℂ) * g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [hgdef, hg1def, Complex.real_smul]
    push_cast
    field_simp
    ring
  · rw [hderiv_G _ (by positivity)]
    show ((c * y : ℝ) : ℂ) * ((1 / c) • g1 (c * y / c)) + (3 / 2 : ℂ) * g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [hgdef, hg1def, Complex.real_smul]
    push_cast
    field_simp
    ring

theorem stepB (κ lam : ℂ) (hκ : κ ≠ 0) (ν : ℝ) (hν1 : 1 ≤ ν) (hνC : ((ν : ℝ) : ℂ) ^ 2 = 1 - 4 * lam)
    (F F₂ : ℝ → ℂ) (c₁ : ℂ)
    (hFd : DifferentiableOn ℝ F (Set.Ioi 0)) (hFd' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (hF₂d : DifferentiableOn ℝ F₂ (Set.Ioi 0))
    (heqF : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - 3 * (y : ℂ) * deriv F y +
      (3 + 4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y =
        8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * c₁ * (y : ℂ) * F₂ y)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ C * y ^ (1 - ε))
    (CF₂ : ℝ) (hCF₂ : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F₂ y‖ ≤ CF₂ * y ^ (1 - 1 / 8 : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → 2 * ‖κ‖ * y ≤ 1 →
      ‖(y : ℂ) * deriv F y - F y‖ ≤ K * y ^ (7 / 4 : ℝ) := by
  have hν0 : 0 ≤ ν := by linarith
  have hνre : ((ν : ℝ) : ℂ).re = ν := Complex.ofReal_re _
  set R : ℝ → ℂ := fun y => 8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * c₁ * (y : ℂ) * F₂ y with hRdef
  obtain ⟨hc, hGd, hGd', hGeq, hGval, hGkill, hGder⟩ := rescale κ lam hκ ((ν : ℝ) : ℂ) hνC F R hFd hFd' heqF
  set c : ℝ := 2 * ‖κ‖ with hcdef
  set G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c) with hGdef
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  obtain ⟨CF, hCF⟩ := hA (1 / 8) (by norm_num)
  obtain ⟨CF', hCF'0, hCF'⟩ := extend_bound F hFd (1 / c) (1 - 1 / 8) CF (by norm_num) hCF
  obtain ⟨CF₂', hCF₂'0, hCF₂'⟩ := extend_bound F₂ hF₂d (1 / c) (1 - 1 / 8) CF₂ (by norm_num) hCF₂
  have hYy : ∀ Y : ℝ, 0 < Y → Y ≤ 1 → 0 < Y / c ∧ Y / c ≤ 1 / c := fun Y hY hY1 =>
    ⟨div_pos hY hc, div_le_div_of_nonneg_right hY1 hc.le⟩
  have hpowsplit : ∀ (Y e : ℝ), 0 < Y → (Y / c) ^ e = c ^ (-e) * Y ^ e := by
    intro Y e hY
    rw [Real.div_rpow hY.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv, mul_comm]

  have hGapOf : ∀ (ε Cε : ℝ), (∀ y : ℝ, 0 < y → y ≤ 1 / c → ‖F y‖ ≤ Cε * y ^ (1 - ε)) →
      ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖G Y‖ ≤ (Cε * c ^ (-(-(1 / 2) - ε))) * Y ^ (-(1 / 2) - ε) := by
    intro ε Cε hCε Y hY hY1
    obtain ⟨hy, hyc⟩ := hYy Y hY hY1
    simp only [hGdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _)]
    calc (Y / c) ^ (-(3 / 2 : ℝ)) * ‖F (Y / c)‖ ≤ (Y / c) ^ (-(3 / 2 : ℝ)) * (Cε * (Y / c) ^ (1 - ε)) := by
          gcongr; exact hCε _ hy hyc
      _ = Cε * ((Y / c) ^ (-(3 / 2 : ℝ)) * (Y / c) ^ (1 - ε)) := by ring
      _ = Cε * (Y / c) ^ (-(1 / 2) - ε) := by rw [← Real.rpow_add hy]; ring_nf
      _ = (Cε * c ^ (-(-(1 / 2) - ε))) * Y ^ (-(1 / 2) - ε) := by rw [hpowsplit Y _ hY]; ring

  set AG : ℝ := 8 * Real.pi * ‖κ‖ * ‖c₁‖ * CF₂' * c ^ (-(3 / 8) : ℝ) with hAG
  have hHb : ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * R (Y / c)‖ ≤ AG * Y ^ (3 / 8 : ℝ) := by
    intro Y hY hY1
    obtain ⟨hy, hyc⟩ := hYy Y hY hY1
    simp only [hRdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _)]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_conj, abs_of_pos hy]
    calc (Y / c) ^ (-(3 / 2 : ℝ)) * (8 * Real.pi * ‖κ‖ * ‖c₁‖ * (Y / c) * ‖F₂ (Y / c)‖)
        ≤ (Y / c) ^ (-(3 / 2 : ℝ)) * (8 * Real.pi * ‖κ‖ * ‖c₁‖ * (Y / c) * (CF₂' * (Y / c) ^ (1 - 1 / 8 : ℝ))) := by
          gcongr; exact hCF₂' _ hy hyc
      _ = 8 * Real.pi * ‖κ‖ * ‖c₁‖ * CF₂' * ((Y / c) ^ (-(3 / 2 : ℝ)) * (Y / c) ^ (1 : ℝ) * (Y / c) ^ (1 - 1 / 8 : ℝ)) := by
          rw [Real.rpow_one]; ring
      _ = 8 * Real.pi * ‖κ‖ * ‖c₁‖ * CF₂' * (Y / c) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_add hy, ← Real.rpow_add hy]; norm_num
      _ = AG * Y ^ (3 / 8 : ℝ) := by rw [hpowsplit Y _ hY, hAG]; ring

  have hback : ∀ (C : ℝ) (y : ℝ), 0 < y →
      ‖((c * y : ℝ) : ℂ) * deriv G (c * y) + (1 / 2 : ℂ) * G (c * y)‖ ≤ C * (c * y) ^ (1 / 4 : ℝ) →
      ‖(y : ℂ) * deriv F y - F y‖ ≤ max C 0 * c ^ (1 / 4 : ℝ) * y ^ (7 / 4 : ℝ) := by
    intro C y hy h
    rw [hGkill y hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _),
      Real.mul_rpow hc.le hy.le] at h
    have hpos := Real.rpow_pos_of_pos hy (3 / 2 : ℝ)
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    rw [← mul_assoc, ← Real.rpow_add hy, show (3 / 2 : ℝ) + -(3 / 2) = 0 by norm_num, Real.rpow_zero, one_mul] at h2
    calc ‖(y : ℂ) * deriv F y - F y‖ ≤ y ^ (3 / 2 : ℝ) * (C * (c ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ))) := h2
      _ ≤ y ^ (3 / 2 : ℝ) * (max C 0 * (c ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ))) := by
          gcongr; exact le_max_left _ _
      _ = max C 0 * c ^ (1 / 4 : ℝ) * (y ^ (3 / 2 : ℝ) * y ^ (1 / 4 : ℝ)) := by ring
      _ = max C 0 * c ^ (1 / 4 : ℝ) * y ^ (7 / 4 : ℝ) := by rw [← Real.rpow_add hy]; norm_num

  have hkill : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → c * y ≤ 1 →
      ‖(y : ℂ) * deriv F y - F y‖ ≤ K * y ^ (7 / 4 : ℝ) := by
    rcases eq_or_lt_of_le hν1 with h1 | h1
    ·
      have hGap := hGapOf (1 / 8) CF' hCF'
      have hGAP := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori ((ν : ℝ) : ℂ)
        (by rw [hνre]; exact hν0) (3 / 8) AG (-(1 / 2) - 1 / 8) _ G _ hGd hGd' hHb hGap hGeq
      obtain ⟨C, hC⟩ := hGAP.1 (1 / 8) (by norm_num)
      have hexp : min (min (1 / 2 + ((ν : ℝ) : ℂ).re) (3 / 8)) (-(1 / 2) - 1 / 8 + 2) - 1 / 8 = (1 / 4 : ℝ) := by
        rw [hνre, ← h1]; norm_num
      refine ⟨max C 0 * c ^ (1 / 4 : ℝ), by positivity, fun y hy hcy => hback C y hy ?_⟩
      have hY : 0 < c * y := by positivity
      have h := hC (c * y) hY hcy
      rw [hexp, show (1 / 2 : ℂ) - ((ν : ℝ) : ℂ) = -(1 / 2 : ℂ) by rw [← h1]; push_cast; norm_num] at h
      convert h using 2; ring
    ·
      set ε₀ : ℝ := min (1 / 8) ((ν - 1) / 2) with hε₀
      have hε₀pos : 0 < ε₀ := lt_min (by norm_num) (by linarith)
      have hε₀le : ε₀ ≤ 1 / 8 := min_le_left _ _
      have hε₀lt : ε₀ < ν - 1 := (min_le_right _ _).trans_lt (by linarith)
      obtain ⟨C0, hC0⟩ := hA ε₀ hε₀pos
      obtain ⟨C0', -, hC0'⟩ := extend_bound F hFd (1 / c) (1 - ε₀) C0 (by linarith) hC0
      have hGap := hGapOf ε₀ C0' hC0'
      have hGAP := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori ((ν : ℝ) : ℂ)
        (by rw [hνre]; exact hν0) (3 / 8) AG (-(1 / 2) - ε₀) _ G _ hGd hGd' hHb hGap hGeq
      have hr : 1 / 2 - ((ν : ℝ) : ℂ).re < -(1 / 2) - ε₀ := by rw [hνre]; linarith
      obtain ⟨C, hC⟩ := hGAP.2 hr (1 / 8) (by norm_num)
      have hexp : min (1 / 2 + ((ν : ℝ) : ℂ).re) (3 / 8) - 1 / 8 = (1 / 4 : ℝ) := by
        rw [hνre, min_eq_right (by linarith)]; norm_num
      refine ⟨max (C + C) 0 * c ^ (1 / 4 : ℝ), by positivity, fun y hy hcy => hback (C + C) y hy ?_⟩
      have hY : 0 < c * y := by positivity
      obtain ⟨hG0, hG1⟩ := hC (c * y) hY hcy
      rw [hexp] at hG0 hG1
      calc ‖((c * y : ℝ) : ℂ) * deriv G (c * y) + (1 / 2 : ℂ) * G (c * y)‖
          ≤ ‖((c * y : ℝ) : ℂ) * deriv G (c * y)‖ + ‖(1 / 2 : ℂ) * G (c * y)‖ := norm_add_le _ _
        _ ≤ C * (c * y) ^ (1 / 4 : ℝ) + 1 / 2 * (C * (c * y) ^ (1 / 4 : ℝ)) := by
            rw [norm_mul (1 / 2 : ℂ), show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
            have h2 : 1 / 2 * ‖G (c * y)‖ ≤ 1 / 2 * (C * (c * y) ^ (1 / 4 : ℝ)) := by linarith [hG0]
            linarith [hG1, h2]
        _ ≤ (C + C) * (c * y) ^ (1 / 4 : ℝ) := by
            have : 0 ≤ C * (c * y) ^ (1 / 4 : ℝ) := le_trans (norm_nonneg _) hG0
            nlinarith
  obtain ⟨K, hK0, hK⟩ := hkill
  exact ⟨K, hK0, fun y hy hcy => hK y hy hcy⟩

end GammaP41

end

open GammaP41

theorem solution
    (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (κ lam lam' : ℂ) (hκ : κ ≠ 0)
    (hU : lam' = lam) (hre : lam.im = 0) (hneg : lam.re ≤ 0)
    (f : ℕ → ℝ → ℂ) (hfN : ∀ y : ℝ, f (n + 1) y = 0)
    (hbdd : ∀ p : Fin (n + 1), ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by
  simp only [hU] at hsys

  have hlam : lam = ((lam.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hre]
  set ν : ℝ := Real.sqrt (1 - 4 * lam.re) with hνdef
  have hν1 : 1 ≤ ν := by
    rw [hνdef]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (1 - 4 * lam.re) := Real.sqrt_le_sqrt (by linarith)
  have hν0 : 0 ≤ ν := by linarith
  have hνsq : ν ^ 2 = 1 - 4 * lam.re := Real.sq_sqrt (by linarith)
  have hνC : ((ν : ℝ) : ℂ) ^ 2 = 1 - 4 * lam := by
    rw [hlam]; exact_mod_cast hνsq
  have hνre : ((ν : ℝ) : ℂ).re = ν := Complex.ofReal_re _

  choose B hB using hbdd
  have hbN : ∀ m : ℕ, m ≤ n + 1 → ∃ Bm : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f m y‖ ≤ Bm := by
    intro m hm
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact ⟨B ⟨m, h⟩, hB ⟨m, h⟩⟩
    · have : m = n + 1 := le_antisymm hm h
      exact ⟨0, fun y _ _ => by rw [this, hfN]; simp⟩

  have hrel : ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y →
      2 * ((n : ℂ) - 2 * (p : ℕ)) * ((y : ℂ) * deriv (f p) y - f p y) +
        8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) *
          (κ * f ((p : ℕ) + 1) y + ((starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ)))) * f ((p : ℕ) - 1) y) = 0 := by
    intro p y hy
    have h1 := ((hsys p).2.2 y hy).1
    have h2 := ((hsys p).2.2 y hy).2
    linear_combination h1 - h2

  have hA : ∀ p : Fin (n + 1), ((n : ℂ) - 2 * (p : ℕ)) ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by
    intro p hq ε hε
    obtain ⟨Bup, hup⟩ := hbN ((p : ℕ) + 1) (by have := p.isLt; omega)
    obtain ⟨Bdn, hdn⟩ := hbN ((p : ℕ) - 1) (by have := p.isLt; omega)
    exact stepA _ hq κ ((starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ)))) (f p) (f ((p : ℕ) + 1)) (f ((p : ℕ) - 1))
      (hsys p).1 Bup Bdn hup hdn (hrel p) ε hε

  obtain ⟨m, hm⟩ := hn
  have hm1 : 1 ≤ m := by omega
  have hmn : m - 1 < n + 1 := by omega
  set p₁ : Fin (n + 1) := ⟨m - 1, hmn⟩ with hp₁
  have hp₁v : ((p₁ : ℕ) : ℂ) = (m : ℂ) - 1 := by
    rw [show (p₁ : ℕ) = m - 1 from rfl]; push_cast [Nat.cast_sub hm1]; ring
  have hnm : (n : ℂ) = (m : ℂ) + (m : ℂ) := by exact_mod_cast hm
  have hq₁ : ((n : ℂ) - 2 * ((p₁ : ℕ) : ℂ)) = 2 := by rw [hp₁v, hnm]; ring
  have hq₁' : ((n : ℂ) - 2 * ((p₁ : ℕ) : ℂ)) ≠ 0 := by rw [hq₁]; norm_num
  have hm2n : m - 1 - 1 < n + 1 := by omega
  set p₂ : Fin (n + 1) := ⟨m - 1 - 1, hm2n⟩ with hp₂
  have hq₂' : ((n : ℂ) - 2 * ((p₂ : ℕ) : ℂ)) ≠ 0 := by
    rw [show (p₂ : ℕ) = m - 1 - 1 from rfl, hnm]
    rcases Nat.lt_or_ge m 2 with h | h
    · have h1 : m = 1 := by omega
      subst h1; norm_num
    · rw [Nat.cast_sub (by omega : 1 ≤ m - 1), Nat.cast_sub hm1]
      push_cast
      intro h0
      have h4 : (4 : ℂ) = 0 := by linear_combination h0
      norm_num at h4

  set F : ℝ → ℂ := f (m - 1) with hFdef
  set F₂ : ℝ → ℂ := f (m - 1 - 1) with hF₂def
  have hFd : DifferentiableOn ℝ F (Set.Ioi 0) := (hsys p₁).1
  have hFd' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0) := (hsys p₁).2.1
  have hF₂d : DifferentiableOn ℝ F₂ (Set.Ioi 0) := (hsys p₂).1
  obtain ⟨CF, hCF⟩ := hA p₁ hq₁' (1 / 8) (by norm_num)
  obtain ⟨CF₂, hCF₂⟩ := hA p₂ hq₂' (1 / 8) (by norm_num)

  set c₁ : ℂ := ((p₁ : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p₁ : ℕ) : ℂ)) with hc₁
  have heqF : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - 3 * (y : ℂ) * deriv F y +
      (3 + 4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y =
        8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * c₁ * (y : ℂ) * F₂ y := by
    intro y hy
    have h2 := ((hsys p₁).2.2 y hy).2
    rw [hq₁] at h2
    have hF1 : f ((p₁ : ℕ)) = F := rfl
    have hF2 : f ((p₁ : ℕ) - 1) = F₂ := rfl
    rw [hF1, hF2] at h2
    simp only [hc₁]
    push_cast at h2 ⊢
    linear_combination h2

  obtain ⟨K, hK0, hK⟩ := stepB κ lam hκ ν hν1 hνC F F₂ c₁ hFd hFd' hF₂d heqF (hA p₁ hq₁') (max CF₂ 0)
    (rpow_bound_mono le_rfl hCF₂)
  set c : ℝ := 2 * ‖κ‖ with hcdef
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc : 0 < c := by positivity

  have hm_eq : (p₁ : ℕ) + 1 = m := by show m - 1 + 1 = m; omega
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set K₀ : ℝ := (4 * K + 8 * Real.pi * ‖κ‖ * ‖c₁‖ * max CF₂ 0) / (8 * Real.pi * ‖κ‖) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hnear : ∀ y : ℝ, 0 < y → y ≤ 1 → c * y ≤ 1 → ‖f m y‖ ≤ K₀ * y ^ (3 / 4 : ℝ) := by
    intro y hy hy1 hcy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := hrel p₁ y hy
    rw [hq₁, hm_eq] at e
    have hF1 : f ((p₁ : ℕ)) = F := rfl
    have hF2 : f ((p₁ : ℕ) - 1) = F₂ := rfl
    rw [hF1, hF2] at e
    have hfm : f m y = -(4 * ((y : ℂ) * deriv F y - F y) + 8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * ((starRingEnd ℂ) κ * c₁ * F₂ y)) /
        (8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ)) := by
      field_simp
      linear_combination e
    rw [hfm, norm_div, norm_neg]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hy]
    rw [div_le_iff₀ (by positivity)]
    have hA1 : ‖4 * ((y : ℂ) * deriv F y - F y) + 8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * ((starRingEnd ℂ) κ * c₁ * F₂ y)‖ ≤
        4 * (K * y ^ (7 / 4 : ℝ)) + 8 * Real.pi * y * (‖κ‖ * ‖c₁‖ * (max CF₂ 0 * y ^ (3 / 4 : ℝ))) := by
      calc _ ≤ ‖4 * ((y : ℂ) * deriv F y - F y)‖ + ‖8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * ((starRingEnd ℂ) κ * c₁ * F₂ y)‖ :=
            norm_add_le _ _
        _ = 4 * ‖(y : ℂ) * deriv F y - F y‖ + 8 * Real.pi * y * (‖κ‖ * ‖c₁‖ * ‖F₂ y‖) := by
            simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
              abs_of_pos Real.pi_pos, abs_of_pos hy, Complex.norm_conj]
        _ ≤ 4 * (K * y ^ (7 / 4 : ℝ)) + 8 * Real.pi * y * (‖κ‖ * ‖c₁‖ * (max CF₂ 0 * y ^ (3 / 4 : ℝ))) := by
            gcongr
            · exact hK y hy hcy
            · exact rpow_bound_mono (by norm_num : (3 / 4 : ℝ) ≤ 1 - 1 / 8) hCF₂ y hy hy1
    refine hA1.trans (le_of_eq ?_)
    have e74 : y ^ (7 / 4 : ℝ) = y ^ (3 / 4 : ℝ) * y := by
      rw [show (7 / 4 : ℝ) = 3 / 4 + 1 by norm_num, Real.rpow_add hy, Real.rpow_one]
    rw [e74, hK₀]
    field_simp

  have hall : ∀ p : Fin (n + 1), ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ Cp * y ^ (3 / 4 : ℝ) := by
    intro p
    by_cases hpm : (p : ℕ) = m
    ·
      obtain ⟨M, hM0, hM⟩ := bdd_Icc (f m) (by have := (hsys p).1; rwa [hpm] at this) (1 / c) 1 (by positivity)
      refine ⟨K₀ + M * c ^ (3 / 4 : ℝ), by positivity, fun y hy hy1 => ?_⟩
      rw [hpm]
      have hy34 : 0 ≤ y ^ (3 / 4 : ℝ) := (Real.rpow_pos_of_pos hy _).le
      rcases le_or_gt (c * y) 1 with hcy | hcy
      · calc ‖f m y‖ ≤ K₀ * y ^ (3 / 4 : ℝ) := hnear y hy hy1 hcy
          _ ≤ (K₀ + M * c ^ (3 / 4 : ℝ)) * y ^ (3 / 4 : ℝ) := by
              rw [add_mul]; linarith [mul_nonneg (mul_nonneg hM0 (Real.rpow_nonneg hc.le (3 / 4 : ℝ))) hy34]
      · have hyc' : 1 / c ≤ y := by rw [div_le_iff₀ hc, mul_comm]; exact hcy.le
        have h1 : 1 ≤ (c * y) ^ (3 / 4 : ℝ) := Real.one_le_rpow hcy.le (by norm_num)
        rw [Real.mul_rpow hc.le hy.le] at h1
        calc ‖f m y‖ ≤ M := hM y ⟨hyc', hy1⟩
          _ ≤ M * (c ^ (3 / 4 : ℝ) * y ^ (3 / 4 : ℝ)) := le_mul_of_one_le_right hM0 h1
          _ ≤ (K₀ + M * c ^ (3 / 4 : ℝ)) * y ^ (3 / 4 : ℝ) := by nlinarith
    · have hq : ((n : ℂ) - 2 * ((p : ℕ) : ℂ)) ≠ 0 := by
        rw [hnm]
        intro h0
        have : ((m : ℂ)) = ((p : ℕ) : ℂ) := by linear_combination h0 / 2
        exact hpm (by exact_mod_cast this.symm)
      obtain ⟨C, hC⟩ := hA p hq (1 / 4) (by norm_num)
      exact ⟨max C 0, le_max_right _ _, rpow_bound_mono (by norm_num : (3 / 4 : ℝ) ≤ 1 - 1 / 4) hC⟩
  choose Cp hCp using hall
  refine ⟨3 / 4, by norm_num, ∑ p : Fin (n + 1), Cp p, fun p y hy hy1 => ?_⟩
  calc ‖f p y‖ ≤ Cp p * y ^ (3 / 4 : ℝ) := (hCp p).2 y hy hy1
    _ ≤ (∑ q : Fin (n + 1), Cp q) * y ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => (hCp q).1) (Finset.mem_univ p))
          (Real.rpow_pos_of_pos hy _).le

end S_LanglandsTunnell_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded
end P2MW
export P2MW.S_LanglandsTunnell_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded (solution)
