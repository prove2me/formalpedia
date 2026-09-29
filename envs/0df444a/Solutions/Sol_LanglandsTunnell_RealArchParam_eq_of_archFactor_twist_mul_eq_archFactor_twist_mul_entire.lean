-- Prove2me | solution 1 for LanglandsTunnell.RealArchParam.eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/aefca70f-fb12-5fd8-aa84-882961228dc5

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire

set_option autoImplicit false

open Complex LanglandsTunnell

namespace Ws47POLE

theorem coeff_eq_zero (u₁ u₂ : ℂ) (h2 : ∀ n : ℕ, u₁ - u₂ ≠ -(2 * (n : ℂ))) (p q : ℂ) (Φ : ℂ → ℂ)
    (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      p * (Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂)) + q * (Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1)) =
        Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1) * Φ s) :
    p = 0 := by

  set I₀ : ℂ → ℂ := fun s => (Gammaℝ (s + u₁))⁻¹ * (Gammaℝ (s + u₂ + 1))⁻¹ with hI₀
  set I₁ : ℂ → ℂ := fun s => (Gammaℝ (s + u₁ + 1))⁻¹ * (Gammaℝ (s + u₂))⁻¹ with hI₁
  have hdI : ∀ c : ℂ, Differentiable ℂ fun s : ℂ => (Gammaℝ (s + c))⁻¹ := fun c =>
    differentiable_Gammaℝ_inv.comp (differentiable_id.add_const c)
  have hI₀d : Differentiable ℂ I₀ := by
    have h2' : Differentiable ℂ fun s : ℂ => (Gammaℝ (s + u₂ + 1))⁻¹ := by
      have := hdI (u₂ + 1); simpa [add_assoc] using this
    exact (hdI u₁).mul h2'
  have hI₁d : Differentiable ℂ I₁ := by
    have h1' : Differentiable ℂ fun s : ℂ => (Gammaℝ (s + u₁ + 1))⁻¹ := by
      have := hdI (u₁ + 1); simpa [add_assoc] using this
    exact h1'.mul (hdI u₂)
  set σ₁ : ℝ := max σ₀ (max (-u₁.re) (-u₂.re)) with hσ₁

  have hent : ∀ s : ℂ, σ₁ < s.re → p * I₀ s + q * I₁ s = I₁ s * Φ s := by
    intro s hs
    have hs0 : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hs1 : -u₁.re < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
    have hs2 : -u₂.re < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
    have hne1 : Gammaℝ (s + u₁) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re]; linarith)
    have hne2 : Gammaℝ (s + u₂) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re]; linarith)
    have hne3 : Gammaℝ (s + u₁ + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re, add_re, one_re]; linarith)
    have hne4 : Gammaℝ (s + u₂ + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [add_re, add_re, one_re]; linarith)
    have := h s hs0
    simp only [hI₀, hI₁]
    field_simp
    linear_combination this
  have heq : (fun s => p * I₀ s + q * I₁ s) = fun s => I₁ s * Φ s := by
    have hA : AnalyticOnNhd ℂ (fun s => p * I₀ s + q * I₁ s) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (((differentiable_const p).mul hI₀d).add ((differentiable_const q).mul hI₁d))
    have hB : AnalyticOnNhd ℂ (fun s => I₁ s * Φ s) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hI₁d.mul hΦ)
    have hopen : IsOpen {s : ℂ | σ₁ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz₀ : ((σ₁ + 1 : ℝ) : ℂ) ∈ {s : ℂ | σ₁ < s.re} := by
      show σ₁ < ((σ₁ + 1 : ℝ) : ℂ).re
      rw [ofReal_re]; linarith
    have hev : (fun s => p * I₀ s + q * I₁ s) =ᶠ[nhds ((σ₁ + 1 : ℝ) : ℂ)] fun s => I₁ s * Φ s :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀) fun s hs => hent s hs
    have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hA hB isPreconnected_univ (Set.mem_univ _) hev
    funext s
    exact this (Set.mem_univ s)

  have hval := congrFun heq (-u₂)
  simp only [hI₀, hI₁] at hval
  have h0 : Gammaℝ (-u₂ + u₂) = 0 := by
    rw [neg_add_cancel, Gammaℝ_eq_zero_iff]; exact ⟨0, by simp⟩
  rw [h0, inv_zero, mul_zero, mul_zero, zero_mul, add_zero] at hval
  have h1 : Gammaℝ (-u₂ + u₂ + 1) ≠ 0 := by
    rw [neg_add_cancel, zero_add]; exact Gammaℝ_ne_zero_of_re_pos (by simp)
  have h3 : Gammaℝ (-u₂ + u₁) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    apply h2 n
    linear_combination hn
  rcases mul_eq_zero.mp hval with hk | hk
  · exact hk
  · exfalso
    rcases mul_eq_zero.mp hk with hk | hk
    · exact h3 (inv_eq_zero.mp hk)
    · exact h1 (inv_eq_zero.mp hk)

theorem coeff_eq_zero' (u₁ u₂ : ℂ) (h2 : ∀ n : ℕ, u₂ - u₁ ≠ -(2 * (n : ℂ))) (p q : ℂ) (Φ : ℂ → ℂ)
    (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      p * (Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂)) + q * (Gammaℝ (s + u₁) * Gammaℝ (s + u₂ + 1)) =
        Gammaℝ (s + u₁ + 1) * Gammaℝ (s + u₂) * Φ s) :
    q = 0 := by
  refine coeff_eq_zero u₂ u₁ h2 q p Φ hΦ σ₀ fun s hs => ?_
  have := h s hs
  linear_combination this

theorem not_even_of_abs_re_lt_one {u₁ u₂ : ℂ} (hu : u₁ ≠ u₂) (htype : |(u₁ - u₂).re| < 1) (n : ℕ) :
    u₁ - u₂ ≠ -(2 * (n : ℂ)) := by
  intro h
  have hre : (u₁ - u₂).re = -(2 * (n : ℝ)) := by
    rw [h]; simp
  rw [hre, abs_neg, abs_of_nonneg (by positivity)] at htype
  have hn : n = 0 := by
    by_contra hn
    have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
    linarith
  subst hn
  apply hu
  have : u₁ - u₂ = 0 := by rw [h]; simp
  exact sub_eq_zero.mp this

theorem archFactor_principal_twist (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s =
      Gammaℝ (s + (u₁ + signShift (a₁ + b))) * Gammaℝ (s + (u₂ + signShift (a₂ + b))) := by
  simp [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]

end Ws47POLE

open Ws47POLE in
theorem solution
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (ha : a₁ ≠ a₂) (hu : u₁ ≠ u₂) (htype : |(u₁ - u₂).re| < 1)
    (P' : RealArchParam) (hP' : P' = .principal u₁ a₁ u₂ a₂ ∨ P' = .principal u₁ a₂ u₂ a₁)
    (ρ : ℂ) (hρ : ρ ≠ 0) (Φ : ℂ → ℂ) (hΦ : Differentiable ℂ Φ) (σ₀ : ℝ)
    (h : ∀ s : ℂ, σ₀ < s.re →
      ρ * (P'.twist 0 0).archFactor s = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 0).archFactor s * Φ s) :
    P' = .principal u₁ a₁ u₂ a₂ := by
  rcases hP' with hP | hP
  · exact hP
  · exfalso
    subst hP
    have hn12 : ∀ n : ℕ, u₁ - u₂ ≠ -(2 * (n : ℂ)) := not_even_of_abs_re_lt_one hu htype
    have hn21 : ∀ n : ℕ, u₂ - u₁ ≠ -(2 * (n : ℂ)) := by
      refine not_even_of_abs_re_lt_one (Ne.symm hu) ?_
      rwa [← neg_sub, neg_re, abs_neg]
    have ha2 : a₂ = a₁ + 1 := by
      have h1 : a₁ = 0 ∨ a₁ = 1 := by fin_cases a₁ <;> first | exact Or.inl rfl | exact Or.inr rfl
      have h2 : a₂ = 0 ∨ a₂ = 1 := by fin_cases a₂ <;> first | exact Or.inl rfl | exact Or.inr rfl
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> first | exact absurd rfl ha | decide
    subst ha2
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have ha1 : a₁ = 0 ∨ a₁ = 1 := by fin_cases a₁ <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases ha1 with rfl | rfl
    ·
      apply hρ
      refine coeff_eq_zero u₁ u₂ hn12 ρ 0 Φ hΦ σ₀ fun s hs => ?_
      have := h s hs
      simp only [archFactor_principal_twist, zero_add, add_zero, signShift_zero, signShift_one, h11] at this
      simp only [add_assoc] at this ⊢
      linear_combination this
    ·
      apply hρ
      refine coeff_eq_zero' u₁ u₂ hn21 0 ρ Φ hΦ σ₀ fun s hs => ?_
      have := h s hs
      simp only [archFactor_principal_twist, zero_add, add_zero, signShift_zero, signShift_one, h11] at this
      simp only [add_assoc] at this ⊢
      linear_combination this

end S_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
end P2MW
export P2MW.S_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire (solution)
