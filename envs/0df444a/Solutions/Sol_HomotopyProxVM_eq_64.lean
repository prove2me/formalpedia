-- Prove2me | solution 1 for HomotopyProxVM.eq_64
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:29:36.219911+00:00
-- url     : https://prove2.me/submissions/39d57fb7-c9c2-4720-8439-01ca143f4f34

import Definitions.Def_HomotopyProxVM_sigmaConst
import Definitions.Def_HomotopyProxVM_tauSeq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open HomotopyProxVM

private theorem sigma_bounds_balance {τ₀ ω a b : ℝ} (hτ₀ : τ₀ ∈ Set.Ioo (0 : ℝ) 1) (hω : ω ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    let σ := sigmaConst τ₀ ω a b
    ω < σ ∧ σ < 1 ∧ (1 - τ₀) * (1 - σ) / τ₀ = (σ - ω) * a / (ω * b) := by
  have hG : 0 < gammaConst a ω b := div_pos ha (mul_pos hω.1 hb)
  have hden : 0 < 1 - τ₀ + τ₀ * gammaConst a ω b := by
    exact add_pos (sub_pos.mpr hτ₀.2) (mul_pos hτ₀.1 hG)
  dsimp only [sigmaConst]
  refine ⟨?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hden).mpr
    nlinarith [mul_pos (sub_pos.mpr hτ₀.2) (sub_pos.mpr hω.2)]
  · apply (div_lt_one hden).mpr
    nlinarith [mul_pos (mul_pos hτ₀.1 hG) (sub_pos.mpr hω.2)]
  · have hΓ : gammaConst a ω b * (ω*b) = a := by
      dsimp only [gammaConst]
      exact div_mul_cancel₀ _ (mul_pos hω.1 hb).ne'
    field_simp [hden.ne', hτ₀.1.ne', hω.1.ne', hb.ne']
    linear_combination τ₀ * (1 - τ₀) * (1 - ω) * hΓ

theorem solution {τ₀ ω a b : ℝ} (hτ₀ : τ₀ ∈ Set.Ioo (0 : ℝ) 1) (hω : ω ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    let σ := sigmaConst τ₀ ω a b
    let C₁ := (σ - ω) * a / (ω * b)
    let τ := tauSeq τ₀ σ
    ∀ k : ℕ, 0 < τ k ∧ τ k < τ (k + 1) ∧ τ (k + 1) ≤ 1 ∧
      τ (k + 1) ≤ τ k + C₁ * σ ^ k * τ k * τ (k + 1) ∧
      0 < 1 - τ k ∧ 1 - τ k ≤ (1 - τ₀) * σ ^ k / τ₀ := by
  let σ := sigmaConst τ₀ ω a b
  have hs : ω < σ ∧ σ < 1 ∧ (1 - τ₀) * (1 - σ) / τ₀ = (σ - ω) * a / (ω * b) :=
    sigma_bounds_balance hτ₀ hω ha hb
  have hs0 : 0 < σ := lt_trans hω.1 hs.1
  have hu : 0 < 1 - τ₀ := sub_pos.mpr hτ₀.2
  let D : ℕ → ℝ := fun k => τ₀ + (1 - τ₀) * σ ^ k
  have hD (k : ℕ) : 0 < D k :=
    add_pos hτ₀.1 (mul_pos hu (pow_pos hs0 k))
  have hrepr (k : ℕ) : tauSeq τ₀ σ k = τ₀ / D k := by
    dsimp only [tauSeq]
    change 1 - (1 - τ₀) * σ ^ k / D k = τ₀ / D k
    apply (eq_div_iff (hD k).ne').mpr
    field_simp [(hD k).ne']
    dsimp only [D]
    ring
  change ∀ k : ℕ, 0 < tauSeq τ₀ σ k ∧ tauSeq τ₀ σ k < tauSeq τ₀ σ (k + 1) ∧
    tauSeq τ₀ σ (k + 1) ≤ 1 ∧
    tauSeq τ₀ σ (k + 1) ≤ tauSeq τ₀ σ k + ((σ - ω) * a / (ω * b)) * σ ^ k *
      tauSeq τ₀ σ k * tauSeq τ₀ σ (k + 1) ∧
    0 < 1 - tauSeq τ₀ σ k ∧ 1 - tauSeq τ₀ σ k ≤ (1 - τ₀) * σ ^ k / τ₀
  intro k
  have hstep : D (k + 1) < D k := by
    dsimp only [D]
    rw [pow_succ]
    nlinarith [mul_pos (mul_pos hu (pow_pos hs0 k)) (sub_pos.mpr hs.2.1)]
  have hlarge (j : ℕ) : τ₀ ≤ D j :=
    le_add_of_nonneg_right (mul_nonneg hu.le (pow_nonneg hs0.le j))
  have hrec : τ₀ / D (k + 1) = τ₀ / D k +
      ((1 - τ₀) * (1 - σ) / τ₀) * σ ^ k * (τ₀ / D k) * (τ₀ / D (k + 1)) := by
    field_simp [hτ₀.1.ne', (hD k).ne', (hD (k + 1)).ne']
    dsimp only [D]
    rw [pow_succ]
    ring
  have hcomp : 1 - tauSeq τ₀ σ k = (1 - τ₀) * σ ^ k / D k := by
    dsimp only [tauSeq, D]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrepr]
    exact div_pos hτ₀.1 (hD k)
  · rw [hrepr, hrepr]
    apply (div_lt_div_iff₀ (hD k) (hD (k + 1))).mpr
    exact mul_lt_mul_of_pos_left hstep hτ₀.1
  · rw [hrepr]
    exact (div_le_one (hD (k + 1))).mpr (hlarge (k + 1))
  · rw [hrepr, hrepr, ← hs.2.2]
    exact hrec.le
  · rw [hcomp]
    exact div_pos (mul_pos hu (pow_pos hs0 k)) (hD k)
  · rw [hcomp]
    exact div_le_div_of_nonneg_left (mul_nonneg hu.le (pow_nonneg hs0.le k)) hτ₀.1 (hlarge k)

#print axioms solution
