-- Prove2me | solution 1 for IQCAlg.ConvexIQC.remark_rho_mono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:48:41.346358+00:00
-- url     : https://prove2.me/submissions/dd41c50b-741b-46c2-aea8-8ce2c78dfa77

import Mathlib

set_option autoImplicit false

theorem solution (w : ℕ → ℝ) (ρ₁ ρ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ)
    (hw : ∀ k : ℕ, 0 ≤ ∑ t ∈ Finset.range (k + 1), (ρ₁ ^ (2 * t))⁻¹ * w t) :
    ∀ k : ℕ, 0 ≤ ∑ t ∈ Finset.range (k + 1), (ρ ^ (2 * t))⁻¹ * w t := by
  intro k
  have hρpos : 0 < ρ := lt_of_lt_of_le hρ₁ hρ
  set c : ℝ := (ρ₁ / ρ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by
    rw [hc]
    have : ρ₁ / ρ ≤ 1 := (div_le_one hρpos).2 hρ
    have h0 : 0 ≤ ρ₁ / ρ := by positivity
    nlinarith
  set a : ℕ → ℝ := fun t => (ρ₁ ^ (2 * t))⁻¹ * w t with ha
  have hS : ∀ n : ℕ, 0 ≤ ∑ t ∈ Finset.range n, a t := by
    intro n
    cases n with
    | zero => simp
    | succ n => exact hw n
  have hid : ∀ t : ℕ, (ρ ^ (2 * t))⁻¹ * w t = a t * c ^ t := by
    intro t
    rw [ha, hc, ← pow_mul, div_pow]
    have h1 : ρ₁ ^ (2 * t) ≠ 0 := by positivity
    have h2 : ρ ^ (2 * t) ≠ 0 := by positivity
    field_simp
  simp_rw [hid]
  have P : ∀ n : ℕ, c ^ n * ∑ t ∈ Finset.range n, a t ≤ ∑ t ∈ Finset.range n, a t * c ^ t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hS (n + 1)
      rw [Finset.sum_range_succ] at hs ⊢
      rw [Finset.sum_range_succ]
      nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hc0 n) (sub_nonneg.2 hc1)) hs, pow_succ c n]
  have := P (k + 1)
  have h0 : 0 ≤ c ^ (k + 1) * ∑ t ∈ Finset.range (k + 1), a t :=
    mul_nonneg (pow_nonneg hc0 _) (hS _)
  linarith
