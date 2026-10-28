-- Prove2me | solution 1 for NonuniformKuramoto.CondII.gamma_analysis
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:44:43.527171+00:00
-- url     : https://prove2.me/submissions/a9815c9d-8e20-4577-a824-03b8de0364e3

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace Aux_NonuniformKuramoto_CondII_gamma_analysis

theorem sinc_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y ≤ Real.pi) :
    Real.sinc y < Real.sinc x := by
  have hy0 : 0 < y := hx.trans hxy
  rw [Real.sinc_of_ne_zero hy0.ne', Real.sinc_of_ne_zero hx.ne']
  have hc := strictConcaveOn_sin_Icc
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hyI : y ∈ Set.Icc 0 Real.pi := ⟨hy0.le, hy⟩
  have ha : 0 < 1 - x / y := by rw [sub_pos, div_lt_one hy0]; exact hxy
  have hb : 0 < x / y := div_pos hx hy0
  have := hc.2 h0 hyI hy0.ne ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at this
  have e : x / y * y = x := by field_simp
  rw [e] at this
  rw [div_lt_div_iff₀ hy0 hx]
  have := mul_lt_mul_of_pos_right this hy0
  have e2 : x / y * Real.sin y * y = x * Real.sin y := by field_simp
  rw [e2] at this
  linarith

theorem sinc_pos {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) : 0 < Real.sinc x := by
  rw [Real.sinc_of_ne_zero hx.ne']
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ) hx

theorem mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases h : x = 0
  · rw [h]; simp
  · rw [Real.sinc_of_ne_zero h]; field_simp

end Aux_NonuniformKuramoto_CondII_gamma_analysis

open NonuniformKuramoto.CondII Aux_NonuniformKuramoto_CondII_gamma_analysis Filter Topology in
theorem solution (ϕmax lc l2 : ℝ) (hϕ0 : 0 ≤ ϕmax) (hϕ1 : ϕmax < Real.pi / 2)
    (hlc : 0 ≤ lc) (hl2 : 0 < l2) :
    ((∃ ρ γ : ℝ, 0 < ρ ∧ ρ < Real.pi ∧ 0 < γ ∧ γ ≤ Real.pi / 2 - ϕmax ∧ γ < ρ ∧
        lc * Real.cos ϕmax / (γ * Real.sinc ρ) < l2) ↔ lc < l2) ∧
    (lc < l2 →
      (∃! ρmax : ℝ, ρmax ∈ Set.Ioc (Real.pi / 2 - ϕmax) Real.pi ∧
        (Real.pi / 2 - ϕmax) * Real.sinc ρmax / Real.cos ϕmax - lc / l2 = 0) ∧
      (∃! γmin : ℝ, γmin ∈ Set.Ico 0 (Real.pi / 2 - ϕmax) ∧
        γmin * Real.sinc γmin / Real.cos ϕmax - lc / l2 = 0)) := by
  set g := Real.pi / 2 - ϕmax with hg
  have hg0 : 0 < g := by linarith
  have hgπ2 : g ≤ Real.pi / 2 := by linarith
  have hgπ : g < Real.pi := by linarith [Real.pi_pos]
  have hc : Real.cos ϕmax = Real.sin g := by rw [hg, Real.sin_pi_div_two_sub]
  have hcpos : 0 < Real.cos ϕmax := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hϕ1⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ρ, γ, hρ0, hρπ, hγ0, hγg, hγρ, hlt⟩
    have hs : 0 < Real.sinc ρ := sinc_pos hρ0 hρπ
    have hden : 0 < γ * Real.sinc ρ := mul_pos hγ0 hs
    have hle : γ * Real.sinc ρ ≤ Real.cos ϕmax := by
      have h1 : Real.sinc ρ ≤ Real.sinc γ := (sinc_strictAnti hγ0 hγρ hρπ.le).le
      have h2 : γ * Real.sinc γ = Real.sin γ := mul_sinc γ
      have h3 : Real.sin γ ≤ Real.sin g := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hgπ2 hγg
      rw [hc]
      nlinarith [mul_le_mul_of_nonneg_left h1 hγ0.le]
    have : lc ≤ lc * Real.cos ϕmax / (γ * Real.sinc ρ) := by
      rw [le_div_iff₀ hden]
      exact mul_le_mul_of_nonneg_left hle hlc
    linarith
  · intro hlt
    have hcont : ContinuousAt (fun ρ => l2 * (g * Real.sinc ρ)) g :=
      (continuous_const.mul (continuous_const.mul Real.continuous_sinc)).continuousAt
    have hval : l2 * (g * Real.sinc g) = l2 * Real.cos ϕmax := by rw [mul_sinc, hc]
    have hlt2 : lc * Real.cos ϕmax < l2 * (g * Real.sinc g) := by
      rw [hval]; exact mul_lt_mul_of_pos_right hlt hcpos
    have hev : ∀ᶠ ρ in 𝓝[>] g, lc * Real.cos ϕmax < l2 * (g * Real.sinc ρ) ∧ ρ < Real.pi ∧ g < ρ := by
      exact (eventually_nhdsWithin_of_eventually_nhds (hcont.eventually (lt_mem_nhds hlt2))).and
        ((eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hgπ)).and eventually_mem_nhdsWithin)
    obtain ⟨ρ, h1, h2, h3⟩ := hev.exists
    refine ⟨ρ, g, by linarith, h2, hg0, le_rfl, h3, ?_⟩
    have hs : 0 < Real.sinc ρ := sinc_pos (by linarith) h2
    rw [div_lt_iff₀ (mul_pos hg0 hs)]
    linarith
  · intro hlt
    have hr : 0 ≤ lc / l2 := div_nonneg hlc hl2.le
    have hr1 : lc / l2 < 1 := by rw [div_lt_one hl2]; exact hlt
    constructor
    · -- ρmax by IVT and strict monotonicity
      set f : ℝ → ℝ := fun ρ => g * Real.sinc ρ / Real.cos ϕmax - lc / l2 with hf
      have hfc : Continuous f :=
        ((continuous_const.mul Real.continuous_sinc).div_const _).sub continuous_const
      have hfg : f g = 1 - lc / l2 := by
        simp only [hf]; rw [mul_sinc, ← hc, div_self hcpos.ne']
      have hfπ : f Real.pi = -(lc / l2) := by
        simp only [hf]; rw [Real.sinc_of_ne_zero Real.pi_pos.ne', Real.sin_pi]; simp
      have hanti : ∀ x y, x ∈ Set.Icc g Real.pi → y ∈ Set.Icc g Real.pi → x < y → f y < f x := by
        intro x y hx hy hxy
        simp only [hf]
        have := sinc_strictAnti (lt_of_lt_of_le hg0 hx.1) hxy hy.2
        have := mul_lt_mul_of_pos_left this hg0
        have := div_lt_div_of_pos_right this hcpos
        linarith
      obtain ⟨ρ, hρI, hρ⟩ := intermediate_value_Icc' hgπ.le hfc.continuousOn
        (show (0 : ℝ) ∈ Set.Icc (f Real.pi) (f g) by rw [hfg, hfπ]; constructor <;> linarith)
      have hρg : ρ ≠ g := by
        rintro rfl; rw [hfg] at hρ; linarith
      refine ⟨ρ, ⟨⟨lt_of_le_of_ne hρI.1 (Ne.symm hρg), hρI.2⟩, hρ⟩, ?_⟩
      rintro ρ' ⟨hρ'I, hρ'⟩
      have hρ'I' : ρ' ∈ Set.Icc g Real.pi := ⟨hρ'I.1.le, hρ'I.2⟩
      have hfρ' : f ρ' = 0 := hρ'
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hanti ρ' ρ hρ'I' hρI h; linarith
      · have := hanti ρ ρ' hρI hρ'I' h; linarith
    · -- γmin via arcsin
      set t := Real.cos ϕmax * (lc / l2) with ht
      have ht0 : 0 ≤ t := mul_nonneg hcpos.le hr
      have htc : t < Real.cos ϕmax := by
        rw [ht]; nlinarith
      have hc1 : Real.cos ϕmax ≤ 1 := Real.cos_le_one _
      have htI : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hgI : g ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, hgπ2⟩
      have heq : ∀ γ, γ * Real.sinc γ / Real.cos ϕmax - lc / l2 = 0 ↔ Real.sin γ = t := by
        intro γ
        rw [mul_sinc, sub_eq_zero, div_eq_iff hcpos.ne', ht]
        constructor <;> intro h <;> linarith
      refine ⟨Real.arcsin t, ⟨⟨Real.arcsin_nonneg.mpr ht0, ?_⟩, ?_⟩, ?_⟩
      · rw [Real.arcsin_lt_iff_lt_sin htI hgI, ← hc]; exact htc
      · rw [heq]; exact Real.sin_arcsin htI.1 htI.2
      · rintro γ ⟨hγI, hγ⟩
        rw [heq] at hγ
        have hγI' : γ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [hγI.1], by linarith [hγI.2]⟩
        have hAI : Real.arcsin t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨Real.neg_pi_div_two_le_arcsin t, Real.arcsin_le_pi_div_two t⟩
        exact Real.injOn_sin hγI' hAI (by rw [hγ, Real.sin_arcsin htI.1 htI.2])
