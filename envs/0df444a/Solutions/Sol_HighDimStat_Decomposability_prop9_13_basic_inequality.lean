-- Prove2me | solution 1 for HighDimStat.Decomposability.prop9_13_basic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:24:33.87551+00:00
-- url     : https://prove2.me/submissions/8ad70efd-97b1-4031-a331-95a4d8608f9e

import Mathlib
import Definitions.Def_HighDimStat_Decomposability_Core

namespace HighDimStat.Decomposability

open scoped RealInnerProductSpace

variable {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]

lemma aux_p913_neg {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (x : Ω) : Φ (-x) = Φ x := by
  have := hΦ.smul_abs (-1) x
  simpa using this

lemma aux_p913_convex {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) : ConvexOn ℝ Set.univ Φ := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  calc Φ (a • x + b • y) ≤ Φ (a • x) + Φ (b • y) := hΦ.triangle _ _
    _ = a • Φ x + b • Φ y := by
      rw [hΦ.smul_abs, hΦ.smul_abs, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul, smul_eq_mul]

lemma aux_p913_lower {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Ω, c * ‖x‖ ≤ Φ x := by
  have hcont : Continuous Φ :=
    continuousOn_univ.mp ((aux_p913_convex hΦ).continuousOn isOpen_univ)
  rcases (Metric.sphere (0 : Ω) 1).eq_empty_or_nonempty with hE | hNE
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [hΦ.nonneg]
    · exfalso
      have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Ω) 1 := by
        simp [norm_smul, hx]
      rw [hE] at hmem
      exact hmem
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      (isCompact_sphere (0 : Ω) 1).exists_isMinOn hNE hcont.continuousOn
    have hx₀n : ‖x₀‖ = 1 := by simpa using hx₀
    have hx₀ne : x₀ ≠ 0 := by
      intro h; rw [h, norm_zero] at hx₀n; exact zero_ne_one hx₀n
    have hc : 0 < Φ x₀ := by
      rcases (hΦ.nonneg x₀).lt_or_eq with h | h
      · exact h
      · exact absurd ((hΦ.eq_zero_iff x₀).mp h.symm) hx₀ne
    refine ⟨Φ x₀, hc, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp [hΦ.nonneg]
    · have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Ω) 1 := by
        simp [norm_smul, hx]
      have h1 : Φ x₀ ≤ Φ (‖x‖⁻¹ • x) := hmin hmem
      rw [hΦ.smul_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))] at h1
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have := mul_le_mul_of_nonneg_left h1 hpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
      linarith [mul_comm (Φ x₀) ‖x‖]

lemma aux_p913_bdd {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (g : Ω) :
    BddAbove {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, g⟫} := by
  obtain ⟨c, hc, hle⟩ := aux_p913_lower hΦ
  refine ⟨‖g‖ / c, ?_⟩
  rintro r ⟨u, hu, rfl⟩
  have h1 : ‖u‖ ≤ 1 / c := by
    rw [le_div_iff₀ hc]
    linarith [hle u, mul_comm c ‖u‖]
  calc ⟪u, g⟫ ≤ ‖u‖ * ‖g‖ := real_inner_le_norm u g
    _ ≤ (1 / c) * ‖g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg g)
    _ = ‖g‖ / c := by ring

lemma aux_p913_dual {Φ : Ω → ℝ} (hΦ : IsRegularizerNorm Φ) (g Δ : Ω) :
    -⟪g, Δ⟫ ≤ dualNorm Φ g * Φ Δ := by
  by_cases hΔ : Δ = 0
  · subst hΔ; simp [(hΦ.eq_zero_iff 0).mpr rfl]
  · have hpos : 0 < Φ Δ := by
      rcases (hΦ.nonneg Δ).lt_or_eq with h | h
      · exact h
      · exact absurd ((hΦ.eq_zero_iff Δ).mp h.symm) hΔ
    set u : Ω := (-(Φ Δ)⁻¹) • Δ with hu
    have hΦu : Φ u ≤ 1 := by
      rw [hu, hΦ.smul_abs, abs_neg, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
    have hmem : ⟪u, g⟫ ∈ {r : ℝ | ∃ u : Ω, Φ u ≤ 1 ∧ r = ⟪u, g⟫} := ⟨u, hΦu, rfl⟩
    have hle : ⟪u, g⟫ ≤ dualNorm Φ g := le_csSup (aux_p913_bdd hΦ g) hmem
    have hinner : ⟪u, g⟫ = -(Φ Δ)⁻¹ * ⟪g, Δ⟫ := by
      rw [hu, real_inner_smul_left, real_inner_comm]
    rw [hinner] at hle
    have := mul_le_mul_of_nonneg_right hle hpos.le
    have e : -(Φ Δ)⁻¹ * ⟪g, Δ⟫ * Φ Δ = -⟪g, Δ⟫ := by
      field_simp
    linarith

lemma aux_p913_grad (Ln : Ω → ℝ) (θstar g Δ : Ω)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar) :
    Ln θstar + ⟪g, Δ⟫ ≤ Ln (θstar + Δ) := by
  set f : ℝ → ℝ := fun t => Ln (θstar + t • Δ) with hf
  have hfconv : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have e : θstar + (a • x + b • y) • Δ = a • (θstar + x • Δ) + b • (θstar + y • Δ) := by
      obtain rfl : b = 1 - a := by linarith
      simp only [smul_eq_mul]
      module
    simp only [hf, smul_eq_mul] at e ⊢
    rw [e]
    exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hline : HasDerivAt (fun t : ℝ => θstar + t • Δ) Δ 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const Δ).const_add θstar
    simpa using this
  have hL : HasFDerivAt Ln (InnerProductSpace.toDual ℝ Ω g) (θstar + (0 : ℝ) • Δ) := by
    simpa using hgrad.hasFDerivAt
  have hderiv : HasDerivAt f ⟪g, Δ⟫ 0 := by
    have := hL.comp_hasDerivAt (0 : ℝ) hline
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  have hs := hfconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    zero_lt_one hderiv
  rw [slope_def_field] at hs
  simp [hf] at hs
  linarith

end HighDimStat.Decomposability

open HighDimStat.Decomposability
open scoped RealInnerProductSpace

theorem solution {Ω : Type*} [NormedAddCommGroup Ω] [InnerProductSpace ℝ Ω] [FiniteDimensional ℝ Ω]
    (Ln Φ : Ω → ℝ) (M Mbar : Submodule ℝ Ω) (θstar θhat g : Ω) (lamN : ℝ)
    (hΦ : IsRegularizerNorm Φ) (hdecomp : IsDecomposable Φ M Mbar)
    (hconv : ConvexOn ℝ Set.univ Ln) (hgrad : HasGradientAt Ln g θstar)
    (hlam : 0 < lamN)
    (hopt : ∀ θ : Ω, Ln θhat + lamN * Φ θhat ≤ Ln θ + lamN * Φ θ)
    (hG : goodEvent Φ g lamN) :
    θhat - θstar ∈ errorCone Φ M Mbar θstar := by
  set Δ := θhat - θstar with hΔ
  have hθhat : θhat = θstar + Δ := by rw [hΔ]; abel
  have h1 := hopt θstar
  have h2 := aux_p913_grad Ln θstar g Δ hconv hgrad
  rw [← hθhat] at h2
  have h3 := aux_p913_dual hΦ g Δ
  have hG' : dualNorm Φ g ≤ lamN / 2 := hG
  have h4 : dualNorm Φ g * Φ Δ ≤ lamN / 2 * Φ Δ :=
    mul_le_mul_of_nonneg_right hG' (hΦ.nonneg Δ)
  have h5 : lamN * (Φ θhat - Φ θstar - Φ Δ / 2) ≤ 0 := by nlinarith
  have h6 : Φ θhat - Φ θstar - Φ Δ / 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hlam hc
    linarith
  -- decomposition
  set a := M.starProjection θstar with ha
  set b := Mᗮ.starProjection θstar with hb
  set d1 := Mbar.starProjection Δ with hd1
  set d2 := Mbarᗮ.starProjection Δ with hd2
  have hθ : a + b = θstar := M.starProjection_add_starProjection_orthogonal θstar
  have hD : d1 + d2 = Δ := Mbar.starProjection_add_starProjection_orthogonal Δ
  have haM : a ∈ M := M.starProjection_apply_mem θstar
  have hd2M : d2 ∈ Mbarᗮ := Mbarᗮ.starProjection_apply_mem Δ
  have hdec : Φ (a + d2) = Φ a + Φ d2 := hdecomp.2 a haM d2 hd2M
  have e1 : a + d2 = θhat + -(b + d1) := by
    rw [hθhat, ← hθ, ← hD]; abel
  have t1 : Φ (a + d2) ≤ Φ θhat + Φ (b + d1) := by
    rw [e1]
    calc Φ (θhat + -(b + d1)) ≤ Φ θhat + Φ (-(b + d1)) := hΦ.triangle _ _
      _ = Φ θhat + Φ (b + d1) := by rw [aux_p913_neg hΦ]
  have t2 : Φ (b + d1) ≤ Φ b + Φ d1 := hΦ.triangle _ _
  have t3 : Φ θstar ≤ Φ a + Φ b := by rw [← hθ]; exact hΦ.triangle _ _
  have t4 : Φ Δ ≤ Φ d1 + Φ d2 := by rw [← hD]; exact hΦ.triangle _ _
  show Φ d2 ≤ 3 * Φ d1 + 4 * Φ b
  linarith
