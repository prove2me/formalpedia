-- Prove2me | solution 1 for InfoShareH2.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:40:39.513651+00:00
-- url     : https://prove2.me/submissions/a2e21e25-0bc8-4466-af33-7ade7b4ed47a

import Mathlib
import Definitions.Def_InfoShareH2_Model

open Filter Topology MeasureTheory Complex

set_option autoImplicit false

theorem solution (f : ℂ → ℂ) (z0 c : ℂ) (θ1 θ2 : ℝ) (h12 : 0 ≤ θ2 - θ1)
    (h12' : θ2 - θ1 ≤ 2 * Real.pi)
    (hf : ∀ e > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ r : ℝ, 0 < r → r < δ → ∀ lam ∈ Set.Icc θ1 θ2,
      ‖((z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) - z0) * f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) - c‖ < e)
    (hint : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun lam : ℝ => f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) * (-I * (r : ℂ) * exp (-(lam : ℂ) * I)))
      volume θ1 θ2) :
    Tendsto (fun r : ℝ => ∫ lam in θ1..θ2,
        f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) * (-I * (r : ℂ) * exp (-(lam : ℂ) * I)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-I * ((θ2 - θ1 : ℝ) : ℂ) * c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hπ := Real.pi_pos
  obtain ⟨e, he⟩ : ∃ e, e = ε / (2 * Real.pi + 1) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; positivity
  obtain ⟨δ, hδ, hfδ⟩ := hf e he0
  have hev : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ
  have hle : θ1 ≤ θ2 := by linarith
  filter_upwards [hev, hint] with r hr hir
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun lam : ℝ => ((z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) - z0) *
      f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) := ⟨_, rfl⟩
  have hFG : ∀ lam : ℝ, f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) * (-I * (r : ℂ) * exp (-(lam : ℂ) * I))
      = -I * G lam := by
    intro lam; rw [hG]; ring
  have hIG : ∀ lam : ℝ, G lam = I * (f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) *
      (-I * (r : ℂ) * exp (-(lam : ℂ) * I))) := by
    intro lam
    rw [hFG]
    linear_combination G lam * I_sq
  have hGi : IntervalIntegrable G volume θ1 θ2 := by
    rw [show G = fun lam : ℝ => I * (f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) *
      (-I * (r : ℂ) * exp (-(lam : ℂ) * I))) from funext hIG]
    exact hir.const_mul I
  have hint_eq : ∫ lam in θ1..θ2, f (z0 + (r : ℂ) * exp (-(lam : ℂ) * I)) *
      (-I * (r : ℂ) * exp (-(lam : ℂ) * I)) = -I * ∫ lam in θ1..θ2, G lam := by
    simp_rw [hFG]
    exact intervalIntegral.integral_const_mul _ _
  have hbound : ‖∫ lam in θ1..θ2, (G lam - c)‖ ≤ e * |θ2 - θ1| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro lam hlam
    rw [Set.uIoc_of_le hle] at hlam
    have := hfδ r hr.1 hr.2 lam ⟨hlam.1.le, hlam.2⟩
    rw [hG]
    exact this.le
  have hsub : ∫ lam in θ1..θ2, (G lam - c) = (∫ lam in θ1..θ2, G lam) - ((θ2 - θ1 : ℝ) : ℂ) * c := by
    rw [intervalIntegral.integral_sub hGi intervalIntegrable_const, intervalIntegral.integral_const,
      Complex.real_smul]
  rw [dist_eq_norm, hint_eq]
  have e3 : -I * (∫ lam in θ1..θ2, G lam) - -I * ((θ2 - θ1 : ℝ) : ℂ) * c
      = -I * ∫ lam in θ1..θ2, (G lam - c) := by
    rw [hsub]; ring
  rw [e3, norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc ‖∫ lam in θ1..θ2, (G lam - c)‖ ≤ e * |θ2 - θ1| := hbound
    _ ≤ e * (2 * Real.pi) := by
        rw [abs_of_nonneg h12]; exact mul_le_mul_of_nonneg_left h12' he0.le
    _ < ε := by
        rw [he, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
