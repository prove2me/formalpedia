-- Prove2me | solution 1 for LiuVanRyzin.segProfit_strictConcave_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:31:33.046896+00:00
-- url     : https://prove2.me/submissions/6da3b375-8314-4076-a0cd-49120db7f421

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

set_option autoImplicit false

namespace LVRAux1c17

open LiuVanRyzin

/-- `φ(t) = (1-γ) t^γ + γ t^(γ-1)`. -/
noncomputable def phi (γ t : ℝ) : ℝ := (1 - γ) * t ^ γ + γ * t ^ (γ - 1)

lemma phi_strictAnti (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (phi γ) (Set.Ioo 0 1) := by
  have hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (phi γ)
      ((1 - γ) * (γ * t ^ (γ - 1)) + γ * ((γ - 1) * t ^ (γ - 1 - 1))) t := by
    intro t ht
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := γ) (Or.inl ht.1.ne')
    have h2 := Real.hasDerivAt_rpow_const (x := t) (p := γ - 1) (Or.inl ht.1.ne')
    exact (h1.const_mul (1 - γ)).add (h2.const_mul γ)
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioo] at ht
    rw [(hd t ht).deriv]
    have hlt : t ^ (γ - 1) < t ^ (γ - 1 - 1) :=
      Real.rpow_lt_rpow_of_exponent_gt ht.1 ht.2 (by linarith)
    have hpos : 0 < γ * (1 - γ) := mul_pos hγ0 (by linarith)
    nlinarith

lemma fill_eq_phi (p₁ p₂ γ v : ℝ) (hp : p₂ < p₁) (hv : p₁ < v) :
    fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁)) = phi γ ((v - p₁) / (v - p₂)) := by
  have hw : 0 < v - p₂ := by linarith
  have hu : 0 < v - p₁ := by linarith
  have hr : 0 < (v - p₁) / (v - p₂) := div_pos hu hw
  unfold fillRate phi
  rw [Real.rpow_sub_one hr.ne']
  set R := ((v - p₁) / (v - p₂)) ^ γ
  field_simp
  ring

lemma ratio_mem (p₁ p₂ v : ℝ) (hp : p₂ < p₁) (hv : p₁ < v) :
    (v - p₁) / (v - p₂) ∈ Set.Ioo (0:ℝ) 1 := by
  have hw : 0 < v - p₂ := by linarith
  have hu : 0 < v - p₁ := by linarith
  refine ⟨div_pos hu hw, ?_⟩
  rw [div_lt_one hw]; linarith

lemma ratio_strictMono (p₁ p₂ : ℝ) (hp : p₂ < p₁) :
    StrictMonoOn (fun v => (v - p₁) / (v - p₂)) (Set.Ioi p₁) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have hwx : 0 < x - p₂ := by linarith
  have hwy : 0 < y - p₂ := by linarith
  show (x - p₁) / (x - p₂) < (y - p₁) / (y - p₂)
  rw [div_lt_div_iff₀ hwx hwy]
  nlinarith

/-- `h(v) = fillRate * (1 + γ (p₁-p₂)/(v-p₁))`, strictly decreasing on `(p₁, ∞)`. -/
lemma h_strictAnti (p₁ p₂ γ : ℝ) (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (fun v => fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁))) (Set.Ioi p₁) := by
  intro x hx y hy hxy
  simp only
  rw [fill_eq_phi p₁ p₂ γ x hp hx, fill_eq_phi p₁ p₂ γ y hp hy]
  exact phi_strictAnti γ hγ0 hγ1 (ratio_mem p₁ p₂ x hp hx) (ratio_mem p₁ p₂ y hp hy)
    (ratio_strictMono p₁ p₂ hp hx hy hxy)

lemma hasDerivAt_g (p₁ p₂ γ v : ℝ) (hp : p₂ < p₁) (hv : p₁ < v) :
    HasDerivAt (fun x => (x - p₂) * fillRate p₁ p₂ γ x)
      (fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁))) v := by
  have hw : 0 < v - p₂ := by linarith
  have hu : 0 < v - p₁ := by linarith
  have hr : 0 < (v - p₁) / (v - p₂) := div_pos hu hw
  have h1 : HasDerivAt (fun x => (x - p₁) / (x - p₂))
      ((1 * (v - p₂) - (v - p₁) * 1) / (v - p₂) ^ 2) v :=
    ((hasDerivAt_id' v).sub_const p₁).div ((hasDerivAt_id' v).sub_const p₂) hw.ne'
  have h2 := h1.rpow_const (p := γ) (Or.inl hr.ne')
  have h3 := ((hasDerivAt_id' v).sub_const p₂).mul h2
  have e : fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁)) =
      1 * ((v - p₁) / (v - p₂)) ^ γ + (v - p₂) *
        ((1 * (v - p₂) - (v - p₁) * 1) / (v - p₂) ^ 2 * γ * ((v - p₁) / (v - p₂)) ^ (γ - 1)) := by
    unfold fillRate
    rw [Real.rpow_sub_one hr.ne']
    set R := ((v - p₁) / (v - p₂)) ^ γ
    field_simp
    ring
  rw [e]
  exact h3

lemma hasDerivAt_P (N Ubar p₁ p₂ α γ v : ℝ) (hp : p₂ < p₁) (hv : p₁ < v) :
    HasDerivAt (segProfit N Ubar p₁ p₂ α γ)
      ((N / Ubar) * (-(p₁ - α) + (p₂ - α) *
        (fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁))))) v := by
  have hfun : segProfit N Ubar p₁ p₂ α γ = fun x => (N / Ubar) *
      ((p₁ - α) * (Ubar - x) + (p₂ - α) * ((x - p₂) * fillRate p₁ p₂ γ x)) := by
    funext x; unfold segProfit; ring
  rw [hfun]
  have A := ((hasDerivAt_id' v).const_sub Ubar).const_mul (p₁ - α)
  have B := (hasDerivAt_g p₁ p₂ γ v hp hv).const_mul (p₂ - α)
  exact ((A.add B).const_mul (N / Ubar)).congr_deriv (by ring)

lemma contOn_P (N Ubar p₁ p₂ α γ : ℝ) (hp : p₂ < p₁) (hγ0 : 0 < γ) :
    ContinuousOn (segProfit N Ubar p₁ p₂ α γ) (Set.Ici p₁) := by
  intro x hx
  simp only [Set.mem_Ici] at hx
  apply ContinuousAt.continuousWithinAt
  have hw : x - p₂ ≠ 0 := by linarith
  have hc : ContinuousAt (fillRate p₁ p₂ γ) x := by
    unfold fillRate
    exact ((continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) hw).rpow_const (Or.inr hγ0.le)
  unfold segProfit
  exact continuousAt_const.mul ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).add
    ((continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).mul hc))

end LVRAux1c17

open LiuVanRyzin in
theorem solution (N Ubar p₁ p₂ α γ : ℝ) (hN : 0 < N)
    (hU : 0 < Ubar) (hα : α < p₂) (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictConcaveOn ℝ (Set.Ici p₁) (segProfit N Ubar p₁ p₂ α γ) ∧
      ∀ v₀ : ℝ, p₁ < v₀ → focLHS p₁ p₂ α γ v₀ = 0 → p₁ ≤ Ubar →
        (if v₀ ≤ Ubar then v₀ else Ubar) ∈ Set.Icc p₁ Ubar ∧
          IsMaxOn (segProfit N Ubar p₁ p₂ α γ) (Set.Icc p₁ Ubar)
            (if v₀ ≤ Ubar then v₀ else Ubar) := by
  have hc : 0 < N / Ubar := div_pos hN hU
  have hpa : 0 < p₂ - α := by linarith
  set H := fun v => fillRate p₁ p₂ γ v * (1 + γ * (p₁ - p₂) / (v - p₁)) with hH
  have hHa : StrictAntiOn H (Set.Ioi p₁) := LVRAux1c17.h_strictAnti p₁ p₂ γ hp hγ0 hγ1
  have hderiv : ∀ v, p₁ < v →
      deriv (segProfit N Ubar p₁ p₂ α γ) v = (N / Ubar) * (-(p₁ - α) + (p₂ - α) * H v) :=
    fun v hv => (LVRAux1c17.hasDerivAt_P N Ubar p₁ p₂ α γ v hp hv).deriv
  have hcont := LVRAux1c17.contOn_P N Ubar p₁ p₂ α γ hp hγ0
  refine ⟨?_, ?_⟩
  · apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici p₁) hcont
    rw [interior_Ici]
    intro x hx y hy hxy
    rw [hderiv x hx, hderiv y hy]
    have := hHa hx hy hxy
    have : (p₂ - α) * H y < (p₂ - α) * H x := mul_lt_mul_of_pos_left this hpa
    exact mul_lt_mul_of_pos_left (by linarith) hc
  · intro v₀ hv₀ hfoc hpU
    have hHv₀ : (p₂ - α) * H v₀ = p₁ - α := by
      have : H v₀ = (p₁ - α) / (p₂ - α) := by
        unfold focLHS at hfoc
        simp only [hH]
        linarith
      rw [this]; field_simp
    have hmono : StrictMonoOn (segProfit N Ubar p₁ p₂ α γ) (Set.Icc p₁ v₀) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (hcont.mono Set.Icc_subset_Ici_self)
      intro x hx
      rw [interior_Icc] at hx
      rw [hderiv x hx.1]
      have h1 := hHa (Set.mem_Ioi.2 hx.1) (Set.mem_Ioi.2 hv₀) hx.2
      have : (p₂ - α) * H v₀ < (p₂ - α) * H x := mul_lt_mul_of_pos_left h1 hpa
      exact mul_pos hc (by linarith)
    have hanti : StrictAntiOn (segProfit N Ubar p₁ p₂ α γ) (Set.Ici v₀) := by
      apply strictAntiOn_of_deriv_neg (convex_Ici _)
        (hcont.mono (Set.Ici_subset_Ici.2 hv₀.le))
      intro x hx
      rw [interior_Ici] at hx
      have hx1 : p₁ < x := lt_trans hv₀ hx
      rw [hderiv x hx1]
      have h1 := hHa (Set.mem_Ioi.2 hv₀) (Set.mem_Ioi.2 hx1) hx
      have : (p₂ - α) * H x < (p₂ - α) * H v₀ := mul_lt_mul_of_pos_left h1 hpa
      exact mul_neg_of_pos_of_neg hc (by linarith)
    split_ifs with hle
    · refine ⟨⟨hv₀.le, hle⟩, isMaxOn_iff.2 fun x hx => ?_⟩
      rcases le_total x v₀ with h | h
      · exact hmono.monotoneOn ⟨hx.1, h⟩ ⟨hv₀.le, le_rfl⟩ h
      · exact hanti.antitoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
    · replace hle := not_le.1 hle
      refine ⟨⟨hpU, le_rfl⟩, isMaxOn_iff.2 fun x hx => ?_⟩
      exact hmono.monotoneOn ⟨hx.1, hx.2.trans hle.le⟩ ⟨hpU, hle.le⟩ hx.2
