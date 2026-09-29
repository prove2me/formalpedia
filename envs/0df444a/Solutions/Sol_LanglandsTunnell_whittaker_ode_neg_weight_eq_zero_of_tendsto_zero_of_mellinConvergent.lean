-- Prove2me | solution 1 for LanglandsTunnell.whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/85b61360-baf9-5bcd-af23-7e09de2d1c18

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent

set_option autoImplicit false

noncomputable section

open Real Complex Filter Topology MeasureTheory Set

namespace LanglandsTunnell
namespace RecVanish

theorem real_core (u u' Q : ℝ → ℝ)
    (hu : ∀ y : ℝ, 0 < y → HasDerivAt u (u' y) y)
    (hu' : ∀ y : ℝ, 0 < y → HasDerivAt u' (Q y * u y) y)
    (hQ : ∀ y : ℝ, 0 < y → 0 < Q y)
    (h0 : Tendsto u (𝓝[>] 0) (𝓝 0)) :
    (∀ y : ℝ, 0 < y → u y = 0) ∨ (∃ y₀ : ℝ, 0 < y₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ y : ℝ, y₀ ≤ y → c ≤ |u y|) := by

  set E : ℝ → ℝ := fun y => u y * u' y with hE
  have hEd : ∀ y : ℝ, 0 < y → HasDerivAt E (u' y * u' y + u y * (Q y * u y)) y := fun y hy =>
    (hu y hy).mul (hu' y hy)
  have hEmono : MonotoneOn E (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · exact fun y hy => (hEd y hy).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; exact fun y hy => (hEd y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]; intro y hy
      rw [(hEd y hy).deriv]
      nlinarith [hQ y hy, mul_self_nonneg (u' y), mul_self_nonneg (u y)]

  have hsq : ∀ y : ℝ, 0 < y → HasDerivAt (fun y => u y ^ 2) (2 * E y) y := by
    intro y hy
    have := (hu y hy).pow 2
    simp [hE, pow_succ, mul_comm, mul_assoc, mul_left_comm] at this ⊢
    exact this
  by_cases hpos : ∃ y₀ : ℝ, 0 < y₀ ∧ 0 < E y₀
  ·
    right
    obtain ⟨y₀, hy₀, hE0⟩ := hpos
    have hu0 : u y₀ ≠ 0 := by
      intro h; rw [hE] at hE0; simp [h] at hE0
    have hmono2 : MonotoneOn (fun y => u y ^ 2) (Ici y₀) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici y₀) ?_ ?_ ?_
      · exact fun y hy => (hsq y (lt_of_lt_of_le hy₀ hy)).continuousAt.continuousWithinAt
      · rw [interior_Ici]; exact fun y hy => (hsq y (hy₀.trans hy)).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]; intro y hy
        rw [(hsq y (hy₀.trans hy)).deriv]
        have : E y₀ ≤ E y := hEmono hy₀ (hy₀.trans hy) hy.le
        linarith
    refine ⟨y₀, hy₀, |u y₀|, abs_pos.2 hu0, fun y hy => ?_⟩
    have h2 : u y₀ ^ 2 ≤ u y ^ 2 := hmono2 self_mem_Ici hy hy
    exact sq_le_sq.mp h2
  ·
    left
    push Not at hpos
    have hanti : AntitoneOn (fun y => u y ^ 2) (Ioi 0) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
      · exact fun y hy => (hsq y hy).continuousAt.continuousWithinAt
      · rw [interior_Ioi]; exact fun y hy => (hsq y hy).differentiableAt.differentiableWithinAt
      · rw [interior_Ioi]; intro y hy
        rw [(hsq y hy).deriv]
        have := hpos y hy
        linarith
    intro y hy
    have hlim : Tendsto (fun ε => u ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using h0.pow 2
    have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), u y ^ 2 ≤ u ε ^ 2 := by
      filter_upwards [Ioo_mem_nhdsGT hy] with ε hε
      exact hanti hε.1 hy hε.2.le
    have : u y ^ 2 ≤ 0 := ge_of_tendsto hlim hle
    nlinarith [sq_nonneg (u y)]

theorem false_of_mellinConvergent_of_le_norm (f : ℝ → ℂ) (s₁ : ℝ) (hs₁ : 0 ≤ s₁)
    (hmel : MellinConvergent f (s₁ : ℂ)) (y₀ : ℝ) (hy₀ : 0 < y₀) (c : ℝ) (hc : 0 < c)
    (hle : ∀ y : ℝ, y₀ ≤ y → c ≤ ‖f y‖) : False := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((s₁ : ℂ) - 1) • f t) (Ioi y₀) :=
    hmel.mono_set (Ioi_subset_Ioi hy₀.le)
  have h2 : IntegrableOn (fun t : ℝ => c * t ^ (s₁ - 1)) (Ioi y₀) := by
    refine Integrable.mono' h1.norm ?_ ?_
    · exact ((measurable_id.pow_const _).const_mul c).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht0 : 0 < t := hy₀.trans ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_smul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, ofReal_re, one_re]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hle t ht.le) (by positivity)
  have h3 : IntegrableOn (fun t : ℝ => t ^ (s₁ - 1)) (Ioi y₀) := by
    have h4 : IntegrableOn (fun t : ℝ => c⁻¹ * (c * t ^ (s₁ - 1))) (Ioi y₀) := h2.const_mul c⁻¹
    refine (integrableOn_congr_fun (fun t _ => ?_) measurableSet_Ioi).mp h4
    field_simp
  rw [integrableOn_Ioi_rpow_iff hy₀] at h3
  linarith

theorem hasDerivAt_re_comp {f : ℝ → ℂ} {y : ℝ} (hf : DifferentiableAt ℝ f y) :
    HasDerivAt (fun t => (f t).re) (deriv f y).re y := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hf.hasDerivAt
  simp at this
  exact this

theorem hasDerivAt_im_comp {f : ℝ → ℂ} {y : ℝ} (hf : DifferentiableAt ℝ f y) :
    HasDerivAt (fun t => (f t).im) (deriv f y).im y := by
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hf.hasDerivAt
  simp at this
  exact this

end LanglandsTunnell.RecVanish

open LanglandsTunnell.RecVanish in
theorem solution
    (ν : ℂ) (hν : (ν ^ 2).im = 0) (hν' : 1 / 4 ≤ (ν ^ 2).re) (k : ℝ) (hk : 0 < k) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((-k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (s₁ : ℝ) (hs₁ : 0 ≤ s₁) (hmel : MellinConvergent f (s₁ : ℂ))
    (y : ℝ) (hy : 0 < y) : f y = 0 := by

  set Q : ℝ → ℝ := fun t => ((ν ^ 2).re - 1 / 4 + 2 * π * k * t + 4 * π ^ 2 * t ^ 2) / t ^ 2 with hQdef
  have hQpos : ∀ t : ℝ, 0 < t → 0 < Q t := by
    intro t ht
    apply div_pos _ (pow_pos ht 2)
    have : 0 < 2 * π * k * t := by positivity
    nlinarith [sq_nonneg t, Real.pi_pos]
  have hν2 : ν ^ 2 = (((ν ^ 2).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hν]

  have hf'' : ∀ t : ℝ, 0 < t → deriv (deriv f) t = ((Q t : ℝ) : ℂ) * f t := by
    intro t ht
    have h := hfeq t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
    have ht2 : (t : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    rw [hQdef]
    push_cast
    rw [hν2] at h
    push_cast at h
    field_simp
    linear_combination 4 * h

  have hd1 : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ f t := fun t ht => hf.differentiableAt (Ioi_mem_nhds ht)
  have hd2 : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ (deriv f) t := fun t ht => hf'.differentiableAt (Ioi_mem_nhds ht)
  have key : ∀ (L : ℂ → ℝ), (L = Complex.re ∨ L = Complex.im) → ∀ t : ℝ, 0 < t → L (f t) = 0 := by
    intro L hL
    have hLd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => L (f t)) (L (deriv f t)) t := by
      rcases hL with rfl | rfl
      · exact fun t ht => hasDerivAt_re_comp (hd1 t ht)
      · exact fun t ht => hasDerivAt_im_comp (hd1 t ht)
    have hLd' : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => L (deriv f t)) (Q t * L (f t)) t := by
      intro t ht
      have hmul : L (deriv (deriv f) t) = Q t * L (f t) := by
        rw [hf'' t ht]
        rcases hL with rfl | rfl
        · simp [Complex.re_ofReal_mul]
        · simp [Complex.im_ofReal_mul]
      rcases hL with rfl | rfl
      · simpa [hmul] using hasDerivAt_re_comp (hd2 t ht)
      · simpa [hmul] using hasDerivAt_im_comp (hd2 t ht)
    have hL0 : Tendsto (fun t => L (f t)) (𝓝[>] 0) (𝓝 0) := by
      rcases hL with rfl | rfl
      · have h__af := (Complex.continuous_re.tendsto 0).comp h0
        simp at h__af
        exact h__af
      · have h__af := (Complex.continuous_im.tendsto 0).comp h0
        simp at h__af
        exact h__af
    rcases real_core (fun t => L (f t)) (fun t => L (deriv f t)) Q hLd hLd' hQpos hL0 with h | h
    · exact h
    · exfalso
      obtain ⟨y₀, hy₀, c, hc, hle⟩ := h
      refine false_of_mellinConvergent_of_le_norm f s₁ hs₁ hmel y₀ hy₀ c hc fun t ht => (hle t ht).trans ?_
      rcases hL with rfl | rfl
      · exact Complex.abs_re_le_norm (f t)
      · exact Complex.abs_im_le_norm (f t)
  apply Complex.ext
  · simpa using key Complex.re (Or.inl rfl) y hy
  · simpa using key Complex.im (Or.inr rfl) y hy

end

end S_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent
end P2MW
export P2MW.S_LanglandsTunnell_whittaker_ode_neg_weight_eq_zero_of_tendsto_zero_of_mellinConvergent (solution)
