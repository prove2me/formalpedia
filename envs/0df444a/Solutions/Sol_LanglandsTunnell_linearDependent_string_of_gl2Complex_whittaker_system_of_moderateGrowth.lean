-- Prove2me | solution 1 for LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/88963322-5d3a-5185-b2b1-749a6c15a098

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth

set_option autoImplicit false

open scoped Real

namespace UniqString

private theorem deriv_comb_eq_zero {F G : ℝ → ℂ} {c₁ c₂ : ℂ}
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hG : DifferentiableOn ℝ G (Set.Ioi 0))
    (h : ∀ y : ℝ, 0 < y → c₁ * F y + c₂ * G y = 0) :
    ∀ y : ℝ, 0 < y → c₁ * deriv F y + c₂ * deriv G y = 0 := by
  intro y hy
  have hmem : Set.Ioi (0 : ℝ) ∈ nhds y := Ioi_mem_nhds hy
  have hFy : DifferentiableAt ℝ F y := hF.differentiableAt hmem
  have hGy : DifferentiableAt ℝ G y := hG.differentiableAt hmem
  have hzero : (fun z => c₁ * F z + c₂ * G z) =ᶠ[nhds y] fun _ => (0 : ℂ) := by
    filter_upwards [hmem] with z hz
    exact h z hz
  have h1 : deriv (fun z => c₁ * F z + c₂ * G z) y = 0 := by
    rw [hzero.deriv_eq, deriv_const]
  have h2 : deriv (fun z => c₁ * F z + c₂ * G z) y = c₁ * deriv F y + c₂ * deriv G y :=
    ((hFy.hasDerivAt.const_mul c₁).add (hGy.hasDerivAt.const_mul c₂)).deriv
  rw [← h2, h1]

private theorem hasDerivAt_rpow_ofReal (b : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => ((t ^ b : ℝ) : ℂ)) (((b * y ^ (b - 1) : ℝ) : ℂ)) y :=
  (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).ofReal_comp

private theorem hasDerivAt_twist {F : ℝ → ℂ} {F' : ℂ} (b : ℝ) {y : ℝ} (hy : 0 < y) (hF : HasDerivAt F F' y) :
    HasDerivAt (fun t => ((t ^ b : ℝ) : ℂ) * F t)
      (((b * y ^ (b - 1) : ℝ) : ℂ) * F y + ((y ^ b : ℝ) : ℂ) * F') y :=
  (hasDerivAt_rpow_ofReal b hy).mul hF

private theorem twist_derivs {F : ℝ → ℂ} (b : ℝ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0)) :
    DifferentiableOn ℝ (fun t => ((t ^ b : ℝ) : ℂ) * F t) (Set.Ioi 0) ∧
    DifferentiableOn ℝ (deriv fun t => ((t ^ b : ℝ) : ℂ) * F t) (Set.Ioi 0) ∧
    (∀ y : ℝ, 0 < y → deriv (fun t => ((t ^ b : ℝ) : ℂ) * F t) y =
      ((b * y ^ (b - 1) : ℝ) : ℂ) * F y + ((y ^ b : ℝ) : ℂ) * deriv F y) ∧
    (∀ y : ℝ, 0 < y → deriv (deriv fun t => ((t ^ b : ℝ) : ℂ) * F t) y =
      ((b * (b - 1) * y ^ (b - 2) : ℝ) : ℂ) * F y + 2 * ((b * y ^ (b - 1) : ℝ) : ℂ) * deriv F y +
        ((y ^ b : ℝ) : ℂ) * deriv (deriv F) y) := by
  have hd1 : ∀ y : ℝ, 0 < y → HasDerivAt (fun t => ((t ^ b : ℝ) : ℂ) * F t)
      (((b * y ^ (b - 1) : ℝ) : ℂ) * F y + ((y ^ b : ℝ) : ℂ) * deriv F y) y := fun y hy =>
    hasDerivAt_twist b hy (hF.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hderiv : ∀ y : ℝ, 0 < y → deriv (fun t => ((t ^ b : ℝ) : ℂ) * F t) y =
      ((b * y ^ (b - 1) : ℝ) : ℂ) * F y + ((y ^ b : ℝ) : ℂ) * deriv F y := fun y hy => (hd1 y hy).deriv

  set E : ℝ → ℂ := fun t => (b : ℂ) * (((t ^ (b - 1) : ℝ) : ℂ) * F t) + ((t ^ b : ℝ) : ℂ) * deriv F t with hE
  have hEeq : ∀ y : ℝ, 0 < y → deriv (fun t => ((t ^ b : ℝ) : ℂ) * F t) y = E y := by
    intro y hy
    rw [hderiv y hy, hE]
    push_cast
    ring
  have hdE : ∀ y : ℝ, 0 < y → HasDerivAt E
      ((b : ℂ) * ((((b - 1) * y ^ (b - 1 - 1) : ℝ) : ℂ) * F y + ((y ^ (b - 1) : ℝ) : ℂ) * deriv F y) +
        (((b * y ^ (b - 1) : ℝ) : ℂ) * deriv F y + ((y ^ b : ℝ) : ℂ) * deriv (deriv F) y)) y := by
    intro y hy
    have h1 := (hasDerivAt_twist (b - 1) hy (hF.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt).const_mul (b : ℂ)
    have h2 := hasDerivAt_twist b hy (hF'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
    exact h1.add h2
  refine ⟨fun y hy => (hd1 y hy).differentiableAt.differentiableWithinAt, ?_, hderiv, ?_⟩
  ·
    have hEd : DifferentiableOn ℝ E (Set.Ioi 0) := fun y hy => (hdE y hy).differentiableAt.differentiableWithinAt
    refine hEd.congr ?_
    intro y hy
    exact hEeq y hy
  · intro y hy
    have hloc : deriv (fun t => ((t ^ b : ℝ) : ℂ) * F t) =ᶠ[nhds y] E := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact hEeq z hz
    rw [hloc.deriv_eq, (hdE y hy).deriv]
    have e : b - 1 - 1 = b - 2 := by ring
    rw [e]
    push_cast
    ring

private theorem scale_derivs {F : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0)) :
    DifferentiableOn ℝ (fun Y => F (Y / c)) (Set.Ioi 0) ∧
    DifferentiableOn ℝ (deriv fun Y => F (Y / c)) (Set.Ioi 0) ∧
    (∀ Y : ℝ, 0 < Y → deriv (fun Y => F (Y / c)) Y = (c⁻¹ : ℂ) * deriv F (Y / c)) ∧
    (∀ Y : ℝ, 0 < Y → deriv (deriv fun Y => F (Y / c)) Y = (c⁻¹ : ℂ) ^ 2 * deriv (deriv F) (Y / c)) := by
  have hdiv : ∀ Y : ℝ, HasDerivAt (fun Y : ℝ => Y / c) c⁻¹ Y := fun Y => by
    simpa [div_eq_mul_inv] using (hasDerivAt_id Y).mul_const c⁻¹
  have hpos : ∀ {Y : ℝ}, 0 < Y → 0 < Y / c := fun hY => div_pos hY hc
  have hd1 : ∀ Y : ℝ, 0 < Y → HasDerivAt (fun Y => F (Y / c)) ((c⁻¹ : ℂ) * deriv F (Y / c)) Y := by
    intro Y hY
    have h := ((hF.differentiableAt (Ioi_mem_nhds (hpos hY))).hasDerivAt).scomp Y (hdiv Y)
    simp [Complex.real_smul] at h
    exact h
  have hderiv : ∀ Y : ℝ, 0 < Y → deriv (fun Y => F (Y / c)) Y = (c⁻¹ : ℂ) * deriv F (Y / c) :=
    fun Y hY => (hd1 Y hY).deriv
  set E : ℝ → ℂ := fun Y => (c⁻¹ : ℂ) * deriv F (Y / c) with hE
  have hdE : ∀ Y : ℝ, 0 < Y → HasDerivAt E ((c⁻¹ : ℂ) * ((c⁻¹ : ℂ) * deriv (deriv F) (Y / c))) Y := by
    intro Y hY
    have h := ((hF'.differentiableAt (Ioi_mem_nhds (hpos hY))).hasDerivAt).scomp Y (hdiv Y)
    have h' : HasDerivAt (fun Y => deriv F (Y / c)) ((c⁻¹ : ℂ) * deriv (deriv F) (Y / c)) Y := by
      simp [Complex.real_smul] at h
      exact h
    exact h'.const_mul _
  refine ⟨fun Y hY => (hd1 Y hY).differentiableAt.differentiableWithinAt, ?_, hderiv, ?_⟩
  · have hEd : DifferentiableOn ℝ E (Set.Ioi 0) := fun Y hY => (hdE Y hY).differentiableAt.differentiableWithinAt
    exact hEd.congr fun Y hY => hderiv Y hY
  · intro Y hY
    have hloc : deriv (fun Y => F (Y / c)) =ᶠ[nhds Y] E := by
      filter_upwards [Ioi_mem_nhds hY] with z hz
      exact hderiv z hz
    rw [hloc.deriv_eq, (hdE Y hY).deriv]
    ring

private theorem top_normal_form (n : ℕ) (κ lam' : ℂ) (hκ : κ ≠ 0) (F : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (hode : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv F) y - ((n : ℂ) + 1) * (y : ℂ) * deriv F y +
        ((n : ℂ) * ((n : ℂ) + 4) / 4 + 4 * lam' - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) *
          F y = 0)
    (hgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖F y‖ ≤ C * y ^ N) :
    let c : ℝ := 2 * ‖κ‖
    let b : ℝ := -((n : ℝ) + 1) / 2
    let H : ℝ → ℂ := fun Y => (((Y / c) ^ b : ℝ) : ℂ) * F (Y / c)
    DifferentiableOn ℝ H (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv H) (Set.Ioi 0) ∧
    (∀ Y : ℝ, 0 < Y →
      (Y : ℂ) ^ 2 * deriv (deriv H) Y +
        (1 / 4 - (1 - 4 * lam') + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * (Y : ℂ) - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * H Y = 0) ∧
    (∃ C N : ℝ, ∀ Y : ℝ, 1 ≤ Y → ‖H Y‖ ≤ C * Y ^ N) := by
  intro c b H
  have hc : 0 < c := by positivity

  set K : ℝ → ℂ := fun t => ((t ^ b : ℝ) : ℂ) * F t with hK
  obtain ⟨hKd, hKd', hK1, hK2⟩ := twist_derivs b hF hF'
  have odeK : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ 2 * deriv (deriv K) y +
        (4 * lam' - 3 / 4 - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * K y = 0 := by
    intro y hy
    have r2 : y ^ (b - 2) * y ^ 2 = y ^ b := by
      rw [Real.rpow_sub hy, Real.rpow_two, div_mul_cancel₀ _ (pow_ne_zero 2 hy.ne')]
    have r1 : y ^ (b - 1) * y = y ^ b := by
      rw [Real.rpow_sub_one hy.ne', div_mul_cancel₀ _ hy.ne']
    have E2 : ((y ^ (b - 2) : ℝ) : ℂ) * (y : ℂ) ^ 2 = ((y ^ b : ℝ) : ℂ) := by exact_mod_cast r2
    have E1 : ((y ^ (b - 1) : ℝ) : ℂ) * (y : ℂ) = ((y ^ b : ℝ) : ℂ) := by exact_mod_cast r1
    have h2 := hK2 y hy
    have hKy : K y = ((y ^ b : ℝ) : ℂ) * F y := rfl
    rw [h2, hKy]
    have hF0 := hode y hy
    have hb : (b : ℂ) = -((n : ℂ) + 1) / 2 := by
      simp only [b]
      push_cast
      ring
    push_cast at hF0 ⊢
    simp only [hb]
    linear_combination ((y ^ b : ℝ) : ℂ) * hF0
      + ((-((n : ℂ) + 1) / 2) * ((-((n : ℂ) + 1) / 2) - 1)) * F y * E2
      + (2 * (-((n : ℂ) + 1) / 2) * deriv F y * (y : ℂ) + deriv (deriv F) y * (y : ℂ) ^ 2 * 0) * E1

  have hHK : H = fun Y => K (Y / c) := rfl
  obtain ⟨hHd, hHd', hH1, hH2⟩ := scale_derivs hc hKd hKd'
  refine ⟨hHK ▸ hHd, hHK ▸ hHd', ?_, ?_⟩
  · intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    have oK := odeK (Y / c) hy
    have h2 : deriv (deriv H) Y = (c⁻¹ : ℂ) ^ 2 * deriv (deriv K) (Y / c) := by rw [hHK]; exact hH2 Y hY
    have hHY : H Y = (((Y / c) ^ b : ℝ) : ℂ) * F (Y / c) := rfl
    rw [h2, hHY]
    simp only [hK] at oK ⊢

    have e1 : (((Y / c : ℝ)) : ℂ) * (c : ℂ) = (Y : ℂ) := by
      exact_mod_cast div_mul_cancel₀ Y hc.ne'
    have e2 : ((c : ℝ) : ℂ) ^ 2 = 4 * ((‖κ‖ ^ 2 : ℝ) : ℂ) := by
      simp only [c]
      push_cast
      ring
    have hc0 : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have e3 : (c : ℂ)⁻¹ * (c : ℂ) = 1 := inv_mul_cancel₀ hc0
    push_cast at oK e2 ⊢
    linear_combination oK
      - 4 * ((((Y / c) ^ b : ℝ) : ℂ) * F (Y / c)) * (Y : ℂ) ^ 2 * (π : ℂ) ^ 2 * ((c : ℂ)⁻¹) ^ 2 * e2
      + 4 * ((((Y / c) ^ b : ℝ) : ℂ) * F (Y / c)) * (Y : ℂ) ^ 2 * (π : ℂ) ^ 2 * ((c : ℂ)⁻¹ * (c : ℂ) + 1) * e3
  ·
    obtain ⟨C, N, hCN⟩ := hgr
    have hb0 : b ≤ 0 := by
      simp only [b]
      have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      linarith

    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x ∈ Set.Icc c⁻¹ 1, ‖F x‖ ≤ B := by
      have hcpt : IsCompact (Set.Icc c⁻¹ (1 : ℝ)) := isCompact_Icc
      have hsub : Set.Icc c⁻¹ (1 : ℝ) ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le (inv_pos.mpr hc) hx.1
      exact hcpt.exists_bound_of_continuousOn (hF.continuousOn.mono hsub)
    set D : ℝ := max B 0 + |C| / c ^ N with hD
    have hD0 : 0 ≤ D := by
      have : 0 ≤ |C| / c ^ N := div_nonneg (abs_nonneg C) (Real.rpow_pos_of_pos hc N).le
      have : 0 ≤ max B 0 := le_max_right _ _
      linarith
    refine ⟨c ^ (-b) * D, max N 0, fun Y hY => ?_⟩
    have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY
    have hx0 : 0 < Y / c := div_pos hY0 hc
    have hYN : 1 ≤ Y ^ max N 0 := Real.one_le_rpow hY (le_max_right _ _)

    have hFx : ‖F (Y / c)‖ ≤ D * Y ^ max N 0 := by
      by_cases hx1 : 1 ≤ Y / c
      · have h1 := hCN (Y / c) hx1
        have h2 : C * (Y / c) ^ N ≤ |C| * (Y / c) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos hx0 N).le
        have h3 : (Y / c) ^ N = Y ^ N / c ^ N := Real.div_rpow hY0.le hc.le N
        have h4 : Y ^ N ≤ Y ^ max N 0 := Real.rpow_le_rpow_of_exponent_le hY (le_max_left _ _)
        have hcN : 0 < c ^ N := Real.rpow_pos_of_pos hc N
        calc ‖F (Y / c)‖ ≤ |C| * (Y / c) ^ N := h1.trans h2
          _ = |C| / c ^ N * Y ^ N := by rw [h3]; ring
          _ ≤ |C| / c ^ N * Y ^ max N 0 :=
              mul_le_mul_of_nonneg_left h4 (div_nonneg (abs_nonneg C) hcN.le)
          _ ≤ D * Y ^ max N 0 := by
              apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hYN)
              simp only [hD]
              linarith [le_max_right B 0]
      · push Not at hx1
        have hmem : Y / c ∈ Set.Icc c⁻¹ 1 := by
          refine ⟨?_, hx1.le⟩
          rw [inv_eq_one_div]
          exact div_le_div_of_nonneg_right hY hc.le
        calc ‖F (Y / c)‖ ≤ B := hB _ hmem
          _ ≤ max B 0 := le_max_left _ _
          _ ≤ D := by simp only [hD]; linarith [div_nonneg (abs_nonneg C) (Real.rpow_pos_of_pos hc N).le]
          _ = D * 1 := (mul_one D).symm
          _ ≤ D * Y ^ max N 0 := mul_le_mul_of_nonneg_left hYN hD0

    have hpow : (Y / c) ^ b ≤ c ^ (-b) := by
      rw [Real.div_rpow hY0.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]
      have h1 : Y ^ b ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY hb0
      have h2 : 0 ≤ (c ^ b)⁻¹ := (inv_pos.mpr (Real.rpow_pos_of_pos hc b)).le
      calc Y ^ b * (c ^ b)⁻¹ ≤ 1 * (c ^ b)⁻¹ := mul_le_mul_of_nonneg_right h1 h2
        _ = (c ^ b)⁻¹ := one_mul _
    have hpow0 : 0 ≤ (Y / c) ^ b := (Real.rpow_pos_of_pos hx0 b).le

    have hHY : H Y = (((Y / c) ^ b : ℝ) : ℂ) * F (Y / c) := rfl
    rw [hHY, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpow0]
    calc (Y / c) ^ b * ‖F (Y / c)‖ ≤ c ^ (-b) * (D * Y ^ max N 0) :=
          mul_le_mul hpow hFx (norm_nonneg _) (Real.rpow_pos_of_pos hc _).le
      _ = c ^ (-b) * D * Y ^ max N 0 := by ring

end UniqString

open UniqString in
theorem solution
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (f g : ℕ → ℝ → ℂ)
    (hf : ∀ p : Fin (n + 1),
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
              f ((p : ℕ) - 1) y = 0))
    (hg : ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (g p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (g p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * g ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              g ((p : ℕ) - 1) y = 0))
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f 0 y‖ ≤ C * y ^ N)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g 0 y‖ ≤ C * y ^ N) :
    ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ p : Fin (n + 1), ∀ y : ℝ, 0 < y → c.1 * f p y + c.2 * g p y = 0 := by

  obtain ⟨c₁, c₂, hc, h0⟩ : ∃ c₁ c₂ : ℂ, (c₁, c₂) ≠ 0 ∧ ∀ y : ℝ, 0 < y → c₁ * f 0 y + c₂ * g 0 y = 0 := by
    obtain ⟨hf0d, hf0d', hf0e⟩ := hf ⟨0, Nat.succ_pos n⟩
    obtain ⟨hg0d, hg0d', hg0e⟩ := hg ⟨0, Nat.succ_pos n⟩

    have odeF : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (f 0)) y - ((n : ℂ) + 1) * (y : ℂ) * deriv (f 0) y +
          ((n : ℂ) * ((n : ℂ) + 4) / 4 + 4 * lam' - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) *
            f 0 y = 0 := by
      intro y hy
      have h := (hf0e y hy).2
      simp only [Nat.cast_zero, mul_zero, sub_zero, zero_mul] at h
      linear_combination h
    have odeG : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (g 0)) y - ((n : ℂ) + 1) * (y : ℂ) * deriv (g 0) y +
          ((n : ℂ) * ((n : ℂ) + 4) / 4 + 4 * lam' - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) *
            g 0 y = 0 := by
      intro y hy
      have h := (hg0e y hy).2
      simp only [Nat.cast_zero, mul_zero, sub_zero, zero_mul] at h
      linear_combination h
    obtain ⟨hHf, hHf', hHfe, hHfg⟩ := top_normal_form n κ lam' hκ (f 0) hf0d hf0d' odeF hfgr
    obtain ⟨hHg, hHg', hHge, hHgg⟩ := top_normal_form n κ lam' hκ (g 0) hg0d hg0d' odeG hggr

    obtain ⟨ν, hν⟩ : ∃ ν : ℂ, ν ^ 2 = 1 - 4 * lam' :=
      ⟨(1 - 4 * lam') ^ ((2 : ℕ)⁻¹ : ℂ), Complex.cpow_nat_inv_pow _ two_ne_zero⟩
    rw [← hν] at hHfe hHge
    obtain ⟨c₁, c₂, hc, hdep⟩ :=
      LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam ν 0 _ _
        hHf hHf' hHfe hHfg hHg hHg' hHge hHgg
    refine ⟨c₁, c₂, hc, fun y hy => ?_⟩

    set c : ℝ := 2 * ‖κ‖ with hcdef
    set b : ℝ := -((n : ℝ) + 1) / 2 with hbdef
    have hcpos : 0 < c := by rw [hcdef]; positivity
    have hYc : c * y / c = y := mul_div_cancel_left₀ y hcpos.ne'
    have h := hdep (c * y) (mul_pos hcpos hy)
    simp only [hYc] at h

    have hyb : ((y ^ b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy b).ne'
    have h' : ((y ^ b : ℝ) : ℂ) * (c₁ * f 0 y + c₂ * g 0 y) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left hyb
  refine ⟨(c₁, c₂), hc, ?_⟩

  suffices H : ∀ p : ℕ, p ≤ n → ∀ y : ℝ, 0 < y → c₁ * f p y + c₂ * g p y = 0 by
    intro p y hy
    exact H p (Nat.lt_succ_iff.mp p.2) y hy
  intro p
  induction p with
  | zero =>
    intro _ y hy
    exact h0 y hy
  | succ p ih =>
    intro hp y hy
    have hp' : p ≤ n := Nat.le_of_succ_le hp
    have key := ih hp'
    obtain ⟨hfd, hfd', hfe⟩ := hf ⟨p, Nat.lt_succ_of_le hp'⟩
    obtain ⟨hgd, hgd', hge⟩ := hg ⟨p, Nat.lt_succ_of_le hp'⟩
    have ef := (hfe y hy).1
    have eg := (hge y hy).1
    have d1 := deriv_comb_eq_zero hfd hgd key
    have d2 := deriv_comb_eq_zero hfd' hgd' d1
    have k0 := key y hy
    have k1 := d1 y hy
    have k2 := d2 y hy
    have hmain : 8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * (c₁ * f (p + 1) y + c₂ * g (p + 1) y) = 0 := by
      linear_combination c₁ * ef + c₂ * eg - (y : ℂ) ^ 2 * k2
        - (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * k1
        - (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
            16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * k0
    have hne : 8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) ≠ 0 := by
      have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hy' : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      have h8 : (8 : ℂ) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h8 hπ) Complex.I_ne_zero) hκ) hy'
    exact (mul_eq_zero.mp hmain).resolve_left hne

end S_LanglandsTunnell_linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
end P2MW
export P2MW.S_LanglandsTunnell_linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth (solution)
