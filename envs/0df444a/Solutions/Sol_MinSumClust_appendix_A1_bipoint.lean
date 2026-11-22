-- Prove2me | solution 1 for MinSumClust.appendix_A1_bipoint
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:37:39.873642+00:00
-- url     : https://prove2.me/submissions/587fb609-d5ba-48c1-b47d-91e9521a57cc

import Mathlib

theorem solution (n k k₁ k₂ : ℕ) (f₁ f₂ c₁ c₂ c opt ε w : ℝ) (hn : 0 < n)
    (hk₁ : k₁ ≤ k) (hk₂ : k < k₂) (hk₂n : k₂ ≤ n) (hf : f₂ < f₁)
    (hstop : f₁ - f₂ ≤ ε * w / n) (hε : 0 ≤ ε) (hw : 0 ≤ w)
    (h₁ : f₁ * k₁ + c₁ ≤ k * f₁ + c * opt) (h₂ : f₂ * k₂ + c₂ ≤ k * f₂ + c * opt) :
    ((k₂ : ℝ) - k) / ((k₂ : ℝ) - k₁) * c₁ + ((k : ℝ) - k₁) / ((k₂ : ℝ) - k₁) * c₂ ≤ ε * w + c * opt ∧
      (w ≤ opt → ε * w + c * opt ≤ (c + ε) * opt) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hk₁' : (k₁:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk₁
  have hk₂' : (k:ℝ) < (k₂:ℝ) := by exact_mod_cast hk₂
  have hk₂n' : (k₂:ℝ) ≤ (n:ℝ) := by exact_mod_cast hk₂n
  set A : ℝ := (k₂:ℝ) - (k:ℝ) with hA
  set B : ℝ := (k:ℝ) - (k₁:ℝ) with hB
  set D : ℝ := (k₂:ℝ) - (k₁:ℝ) with hD
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hD0 : 0 < D := by rw [hD]; linarith
  have hAB : A + B = D := by rw [hA, hB, hD]; ring
  constructor
  · -- first clause: numerator comparison after clearing the denominator
    have hc₁ : c₁ ≤ B * f₁ + c * opt := by
      rw [hB]
      nlinarith
    have hc₂ : c₂ ≤ -A * f₂ + c * opt := by
      rw [hA]
      nlinarith
    have hprod : A * B ≤ D * (n:ℝ) / 4 := by
      have hs : 0 ≤ (A - B)^2 := sq_nonneg (A - B)
      have h1 : 4 * (A * B) ≤ (A + B)^2 := by nlinarith
      rw [hAB] at h1
      have h2 : D^2 ≤ D * (n:ℝ) := by nlinarith
      nlinarith
    have hmain : A * c₁ + B * c₂ ≤ A * B * (f₁ - f₂) + D * (c * opt) := by
      have w1 := mul_le_mul_of_nonneg_left hc₁ hA0
      have w2 := mul_le_mul_of_nonneg_left hc₂ hB0
      nlinarith
    have hstep : A * B * (f₁ - f₂) ≤ D * (ε * w / 4) := by
      have hf' : 0 ≤ f₁ - f₂ := by linarith
      have hAB0 : 0 ≤ A * B := mul_nonneg hA0 hB0
      calc A * B * (f₁ - f₂) ≤ (D * (n:ℝ) / 4) * (ε * w / (n:ℝ)) := by
            apply mul_le_mul hprod hstop hf' (by positivity)
        _ = D * (ε * w / 4) := by
            field_simp [hn'.ne']
    have hεw : 0 ≤ ε * w := mul_nonneg hε hw
    have hfin : A * c₁ + B * c₂ ≤ D * (ε * w + c * opt) := by
      have h1 : D * (ε * w / 4) ≤ D * (ε * w) :=
        mul_le_mul_of_nonneg_left (by linarith) hD0.le
      nlinarith
    have hdiv : A / D * c₁ + B / D * c₂ = (A * c₁ + B * c₂) / D := by
      field_simp
    rw [hdiv]
    rw [div_le_iff₀ hD0]
    linarith
  · -- second clause
    intro hwopt
    have h1 := mul_le_mul_of_nonneg_left hwopt hε
    nlinarith
