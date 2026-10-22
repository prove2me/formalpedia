-- Prove2me | solution 1 for NonlinCG.PropStar.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T03:59:20.54875+00:00
-- url     : https://prove2.me/submissions/91d27bae-5f5f-402f-93f0-8b367426083a

import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting



namespace NonlinCG.PropStar

lemma l41_unit_diff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖u - v‖ ≤ 2 * ‖u - δ • v‖ := by
  have h1 : ‖u - δ • v‖ = ‖δ • u - v‖ := by
    have e1 : ‖u - δ • v‖ ^ 2 = ‖δ • u - v‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_smul_right, inner_smul_left, norm_smul,
        norm_smul, hu, hv, Real.norm_eq_abs, abs_of_nonneg hδ]
      simp only [conj_trivial]
      rw [real_inner_comm]
      ring
    have := abs_eq_abs.mpr (sq_eq_sq_iff_eq_or_eq_neg.mp e1)
    simpa [abs_of_nonneg (norm_nonneg _)] using this
  have h2 : (1 + δ) • (u - v) = (u - δ • v) - (v - δ • u) := by
    rw [add_smul, smul_sub, smul_sub]; module
  have h3 : (1 + δ) * ‖u - v‖ ≤ 2 * ‖u - δ • v‖ := by
    have : ‖(1 + δ) • (u - v)‖ ≤ ‖u - δ • v‖ + ‖v - δ • u‖ := by
      rw [h2]; exact norm_sub_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at this
    have h4 : ‖v - δ • u‖ = ‖δ • u - v‖ := norm_sub_rev _ _
    rw [h4, ← h1] at this
    linarith
  nlinarith [norm_nonneg (u - v)]

theorem lemma41_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, 0 ≤ β k)
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    (∀ k ≥ 1, d k ≠ 0) ∧
      Summable (fun k : ℕ => ‖u d (k + 2) - u d (k + 1)‖ ^ 2) := by
  obtain ⟨γ, hγ, hg⟩ := h43
  have hdne : ∀ k ≥ 1, d k ≠ 0 := by
    intro k hk h0
    have h1 := hD k hk
    rw [h0, inner_zero_right] at h1
    have h2 : 0 < ‖NonlinCG.FRBound.g f x k‖ := lt_of_lt_of_le hγ (hg k hk)
    nlinarith [hσ₃.1, mul_pos hσ₃.1 (pow_pos h2 2)]
  refine ⟨hdne, ?_⟩
  have hZ' := hZ
  unfold NonlinCG.FRBound.ZoutendijkCondition at hZ'
  have hS : Summable (fun k : ℕ => ‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 2 / ‖d (k + 2)‖ ^ 2) := by
    have hZ2 := (summable_nat_add_iff 1).mpr hZ'
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((hZ2.mul_left (1 / (σ₃ ^ 2 * γ ^ 2))))
    have hk : k + 1 + 1 ≥ 1 := by omega
    have hgk : γ ≤ ‖NonlinCG.FRBound.g f x (k + 2)‖ := hg (k + 2) (by omega)
    have hdk : 0 < ‖d (k + 2)‖ := norm_pos_iff.mpr (hdne (k + 2) (by omega))
    have hD2 := hD (k + 2) (by omega)
    have hgp : 0 < ‖NonlinCG.FRBound.g f x (k + 2)‖ := lt_of_lt_of_le hγ hgk
    have hsq : σ₃ * ‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 2 ≤
        |inner ℝ (NonlinCG.FRBound.g f x (k + 2)) (d (k + 2))| := by
      have := neg_le_abs (inner ℝ (NonlinCG.FRBound.g f x (k + 2)) (d (k + 2)))
      linarith
    have hsq2 : σ₃ ^ 2 * ‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 4 ≤
        inner ℝ (NonlinCG.FRBound.g f x (k + 2)) (d (k + 2)) ^ 2 := by
      rw [← sq_abs (inner ℝ _ _)]
      have h0 : 0 ≤ σ₃ * ‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 2 := by
        have := hσ₃.1; positivity
      calc σ₃ ^ 2 * ‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 4
          = (σ₃ * ‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 2) ^ 2 := by ring
        _ ≤ _ := pow_le_pow_left₀ h0 hsq 2
    show _ ≤ 1 / (σ₃ ^ 2 * γ ^ 2) * (inner ℝ (NonlinCG.FRBound.g f x (k + 1 + 1)) (d (k + 1 + 1)) ^ 2 / ‖d (k + 1 + 1)‖ ^ 2)
    have e : k + 1 + 1 = k + 2 := rfl
    rw [e]
    set G := ‖NonlinCG.FRBound.g f x (k + 2)‖
    set D := ‖d (k + 2)‖
    have hσ := hσ₃.1
    rw [div_le_iff₀ (by positivity), one_div, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc G ^ 2 * (σ₃ ^ 2 * γ ^ 2) = σ₃ ^ 2 * (G ^ 2 * γ ^ 2) := by ring
      _ ≤ σ₃ ^ 2 * (G ^ 2 * G ^ 2) := by gcongr
      _ = σ₃ ^ 2 * G ^ 4 := by ring
      _ ≤ _ := by refine hsq2.trans (le_of_eq ?_); field_simp
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hS.mul_left 4)
  have hk2 : k + 2 ≥ 2 := by omega
  have hdk : 0 < ‖d (k + 2)‖ := norm_pos_iff.mpr (hdne (k + 2) (by omega))
  have hdk1 : 0 < ‖d (k + 1)‖ := norm_pos_iff.mpr (hdne (k + 1) (by omega))
  have hrec := hrun.2.1 (k + 2) hk2
  have hrec' : d (k + 2) = -NonlinCG.FRBound.g f x (k + 2) + β (k + 2) • d (k + 1) := by
    simpa using hrec
  set δ : ℝ := β (k + 2) * ‖d (k + 1)‖ / ‖d (k + 2)‖ with hδ
  have hδ0 : 0 ≤ δ := by
    have := hβ (k + 2) hk2
    positivity
  have hu2 : ‖u d (k + 2)‖ = 1 := by
    unfold u; rw [norm_smul, norm_inv, norm_norm]; field_simp
  have hu1 : ‖u d (k + 1)‖ = 1 := by
    unfold u; rw [norm_smul, norm_inv, norm_norm]; field_simp
  have e1 : d (k + 2) - β (k + 2) • d (k + 1) = -NonlinCG.FRBound.g f x (k + 2) := by
    rw [hrec']; abel
  have key : u d (k + 2) - δ • u d (k + 1) = -(‖d (k + 2)‖⁻¹) • NonlinCG.FRBound.g f x (k + 2) := by
    have e2 : u d (k + 2) - δ • u d (k + 1) = ‖d (k + 2)‖⁻¹ • (d (k + 2) - β (k + 2) • d (k + 1)) := by
      simp only [u, hδ, smul_sub, smul_smul]
      have : β (k + 2) * ‖d (k + 1)‖ / ‖d (k + 2)‖ * ‖d (k + 1)‖⁻¹ = ‖d (k + 2)‖⁻¹ * β (k + 2) := by
        field_simp
      rw [this]
    rw [e2, e1, smul_neg, neg_smul]
  have h1 := l41_unit_diff _ _ hu2 hu1 δ hδ0
  rw [key, norm_smul, norm_neg, norm_inv, norm_norm] at h1
  have h3 : ‖u d (k + 2) - u d (k + 1)‖ ^ 2 ≤ (2 * (‖d (k + 2)‖⁻¹ * ‖NonlinCG.FRBound.g f x (k + 2)‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ‖u d (k + 2) - u d (k + 1)‖ ^ 2 ≤ _ := h3
    _ = 4 * (‖NonlinCG.FRBound.g f x (k + 2)‖ ^ 2 / ‖d (k + 2)‖ ^ 2) := by
      field_simp; ring

end NonlinCG.PropStar

open NonlinCG.PropStar


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, 0 ≤ β k)
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    (∀ k ≥ 1, d k ≠ 0) ∧
      Summable (fun k : ℕ => ‖u d (k + 2) - u d (k + 1)‖ ^ 2) := by
  exact lemma41_core f β α x d σ₃ hrun hβ hZ hσ₃ hD h43
