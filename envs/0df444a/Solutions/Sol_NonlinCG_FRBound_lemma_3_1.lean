-- Prove2me | solution 1 for NonlinCG.FRBound.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:05:58.008603+00:00
-- url     : https://prove2.me/submissions/4aa84d22-0916-449f-99d4-eb0bb177a061

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

set_option autoImplicit false

namespace NCGAux

open NonlinCG.FRBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma geom (σ : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), σ ^ j = 1 + σ * ∑ j ∈ Finset.range k, σ ^ j := by
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma core (f : E → ℝ) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₂ : ℝ)
    (hrun : IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, |β k| ≤ betaFR f x k)
    (hσ : 0 < σ₂ ∧ σ₂ < 1 / 2)
    (hls : ∀ k ≥ 1,
      |inner ℝ (gradient f (x k + α k • d k)) (d k)| ≤ -σ₂ * inner ℝ (g f x k) (d k))
    (hg : ∀ k ≥ 1, g f x k ≠ 0) :
    ∀ k, 1 ≤ k →
      -(∑ j ∈ Finset.range k, σ₂ ^ j) ≤ inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 ∧
      inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 ≤ -2 + ∑ j ∈ Finset.range k, σ₂ ^ j := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : g f x 1 ≠ 0 := hg 1 le_rfl
    have hn : 0 < ‖g f x 1‖ ^ 2 := by positivity
    have : inner ℝ (g f x 1) (d 1) / ‖g f x 1‖ ^ 2 = -1 := by
      rw [hrun.1, inner_neg_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [this]
    norm_num
  | succ k hk ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hgk : g f x k ≠ 0 := hg k hk
    have hgk1 : g f x (k + 1) ≠ 0 := hg (k + 1) (by omega)
    have hnk : 0 < ‖g f x k‖ ^ 2 := by positivity
    have hnk1 : 0 < ‖g f x (k + 1)‖ ^ 2 := by positivity
    have hd : d (k + 1) = -g f x (k + 1) + β (k + 1) • d k := by
      have := hrun.2.1 (k + 1) (by omega)
      simpa using this
    have hinner : inner ℝ (g f x (k + 1)) (d (k + 1)) =
        -‖g f x (k + 1)‖ ^ 2 + β (k + 1) * inner ℝ (g f x (k + 1)) (d k) := by
      rw [hd, inner_add_right, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hx : x (k + 1) = x k + α k • d k := (hrun.2.2 k hk).2
    have hwolfe : |inner ℝ (g f x (k + 1)) (d k)| ≤ -σ₂ * inner ℝ (g f x k) (d k) := by
      have := hls k hk
      rw [← hx] at this
      exact this
    have hb : |β (k + 1)| ≤ ‖g f x (k + 1)‖ ^ 2 / ‖g f x k‖ ^ 2 := by
      have := hβ (k + 1) (by omega)
      simpa [betaFR] using this
    -- t := β ⟨g_{k+1}, d_k⟩ / ‖g_{k+1}‖²
    set t : ℝ := β (k + 1) * inner ℝ (g f x (k + 1)) (d k) / ‖g f x (k + 1)‖ ^ 2 with ht
    have hr : inner ℝ (g f x (k + 1)) (d (k + 1)) / ‖g f x (k + 1)‖ ^ 2 = -1 + t := by
      rw [hinner, ht]; field_simp
    have hrk : -σ₂ * (inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2) =
        (-σ₂ * inner ℝ (g f x k) (d k)) / ‖g f x k‖ ^ 2 := by ring
    have habs : |t| ≤ -σ₂ * (inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2) := by
      rw [hrk, ht, abs_div, abs_mul, abs_of_pos hnk1, div_le_div_iff₀ hnk1 hnk]
      have h1 : |β (k + 1)| * |inner ℝ (g f x (k + 1)) (d k)| ≤
          (‖g f x (k + 1)‖ ^ 2 / ‖g f x k‖ ^ 2) * (-σ₂ * inner ℝ (g f x k) (d k)) :=
        mul_le_mul hb hwolfe (abs_nonneg _) (by positivity)
      have h2 : (‖g f x (k + 1)‖ ^ 2 / ‖g f x k‖ ^ 2) * (-σ₂ * inner ℝ (g f x k) (d k)) * ‖g f x k‖ ^ 2
          = ‖g f x (k + 1)‖ ^ 2 * (-σ₂ * inner ℝ (g f x k) (d k)) := by
        field_simp
      have h3 := mul_le_mul_of_nonneg_right h1 hnk.le
      rw [h2] at h3
      linarith
    rw [hr, geom]
    have := abs_le.1 habs
    obtain ⟨hσ0, -⟩ := hσ
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left ih1 hσ0.le]
    · nlinarith [mul_le_mul_of_nonneg_left ih1 hσ0.le]


lemma sum_le (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1 / 2) (k : ℕ) :
    ∑ j ∈ Finset.range k, σ ^ j ≤ 1 / (1 - σ) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have : 0 < 1 - σ := by linarith
    positivity
  | succ k ih =>
    rw [geom]
    have hpos : 0 < 1 - σ := by linarith
    have : σ * ∑ j ∈ Finset.range k, σ ^ j ≤ σ * (1 / (1 - σ)) := mul_le_mul_of_nonneg_left ih h0.le
    have e : 1 + σ * (1 / (1 - σ)) = 1 / (1 - σ) := by field_simp; ring
    linarith

lemma inv_lt_two (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1 / 2) : 1 / (1 - σ) < 2 := by
  have hpos : 0 < 1 - σ := by linarith
  rw [div_lt_iff₀ hpos]; linarith

end NCGAux

open NCGAux NonlinCG.FRBound in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E)
    (σ₂ : ℝ) (hA : Assumptions21 f (x 1)) (hrun : IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, |β k| ≤ betaFR f x k)
    (hσ : 0 < σ₂ ∧ σ₂ < 1 / 2)
    (hls : ∀ k ≥ 1,
      |inner ℝ (gradient f (x k + α k • d k)) (d k)| ≤ -σ₂ * inner ℝ (g f x k) (d k))
    (hg : ∀ k ≥ 1, g f x k ≠ 0) :
    ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0 ∧
      -(∑ j ∈ Finset.range k, σ₂ ^ j) ≤ inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 ∧
      inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 ≤ -2 + ∑ j ∈ Finset.range k, σ₂ ^ j := by
  intro k hk
  obtain ⟨h1, h2⟩ := core f β α x d σ₂ hrun hβ hσ hls hg k hk
  refine ⟨?_, h1, h2⟩
  have hn : 0 < ‖g f x k‖ ^ 2 := by have := hg k hk; positivity
  have hS := (sum_le σ₂ hσ.1 hσ.2 k).trans (inv_lt_two σ₂ hσ.1 hσ.2).le
  have hS' : ∑ j ∈ Finset.range k, σ₂ ^ j < 2 :=
    lt_of_le_of_lt (sum_le σ₂ hσ.1 hσ.2 k) (inv_lt_two σ₂ hσ.1 hσ.2)
  have : inner ℝ (g f x k) (d k) / ‖g f x k‖ ^ 2 < 0 := by linarith
  exact (div_neg_iff.1 this).elim (fun h => absurd h.2 (not_lt.2 hn.le)) (fun h => h.1)
