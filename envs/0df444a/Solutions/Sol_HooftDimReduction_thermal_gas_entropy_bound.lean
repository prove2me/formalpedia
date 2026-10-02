-- Prove2me | solution 1 for HooftDimReduction.thermal_gas_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:00:28.629072+00:00
-- url     : https://prove2.me/submissions/b87b10b7-1bc7-4c4a-b75c-a0b78cc3866b

import Mathlib

set_option autoImplicit false

lemma dfb7_pow_rpow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (a : ℝ) : (x ^ n) ^ a = x ^ ((n : ℝ) * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

lemma dfb7_rpow_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (a : ℝ) : (x ^ a) ^ n = x ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem solution (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C₃ C₄ C₅ : ℝ, 0 < C₃ ∧ 0 < C₄ ∧ 0 < C₅ ∧
      ∀ Z R T : ℝ, 0 < Z → 0 < R → 0 < T →
        2 * (C₁ * Z * (4 / 3 * Real.pi * R ^ 3) * T ^ 4) < R →
          T < C₃ * Z ^ (-(1 / 4 : ℝ)) * (4 / 3 * Real.pi * R ^ 3) ^ (-(1 / 6 : ℝ)) ∧
          C₂ * Z * (4 / 3 * Real.pi * R ^ 3) * T ^ 3 <
            C₄ * Z ^ (1 / 4 : ℝ) * (4 / 3 * Real.pi * R ^ 3) ^ (1 / 2 : ℝ) ∧
          C₂ * Z * (4 / 3 * Real.pi * R ^ 3) * T ^ 3 <
            C₅ * Z ^ (1 / 4 : ℝ) * (4 * Real.pi * R ^ 2) ^ (3 / 4 : ℝ) := by
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 4 / 3 * Real.pi := ⟨_, rfl⟩
  rw [← hkdef]
  have hk : 0 < k := by rw [hkdef]; positivity
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (1 / (2 * C₁ * k)) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hc4 : c ^ 4 = 1 / (2 * C₁ * k) := by
    rw [hcdef, dfb7_rpow_pow _ (by positivity)]; norm_num
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = k ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = k ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = (4 * Real.pi) ^ (3 / 4 : ℝ) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  have hσ : 0 < σ := by rw [hσdef]; positivity
  have hτ : 0 < τ := by rw [hτdef]; positivity
  refine ⟨κ * c, C₂ * k * c ^ 3 / σ, C₂ * k * c ^ 3 / τ, by positivity, by positivity,
    by positivity, ?_⟩
  intro Z R T hZ hR hT hS
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = Z ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hW : 0 < W := by rw [hWdef]; positivity
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hW4 : W ^ 4 = Z := by rw [hWdef, dfb7_rpow_pow _ hZ.le]; norm_num
  have hρ2 : ρ ^ 2 = R := by rw [hρdef, dfb7_rpow_pow _ hR.le]; norm_num
  have hρ3 : ρ ^ 3 = R ^ (3 / 2 : ℝ) := by rw [hρdef, dfb7_rpow_pow _ hR.le]; norm_num
  have key : W * ρ * T < c := by
    have h1 : (W * ρ * T) ^ 4 < c ^ 4 := by
      rw [hc4, mul_pow, mul_pow, hW4, show ρ ^ 4 = R ^ 2 by rw [← hρ2]; ring]
      rw [lt_div_iff₀ (by positivity)]
      have e : R * (Z * R ^ 2 * T ^ 4 * (2 * C₁ * k)) = 2 * (C₁ * Z * (k * R ^ 3) * T ^ 4) := by
        ring
      have h2 : R * (Z * R ^ 2 * T ^ 4 * (2 * C₁ * k)) < R * 1 := by rw [e]; linarith
      exact lt_of_mul_lt_mul_left h2 hR.le
    exact lt_of_pow_lt_pow_left₀ 4 hc.le h1
  have h3 : (W * ρ * T) ^ 3 < c ^ 3 := pow_lt_pow_left₀ key (by positivity) (by norm_num)
  have hZm : Z ^ (-(1 / 4 : ℝ)) = W⁻¹ := by rw [Real.rpow_neg hZ.le, hWdef]
  have hV6 : (k * R ^ 3) ^ (-(1 / 6 : ℝ)) = (κ * ρ)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.mul_rpow hk.le (by positivity),
      dfb7_pow_rpow _ hR.le, hκdef, hρdef]
    norm_num
  have hV2 : (k * R ^ 3) ^ (1 / 2 : ℝ) = σ * ρ ^ 3 := by
    rw [Real.mul_rpow hk.le (by positivity), dfb7_pow_rpow _ hR.le, hσdef, hρ3]
    norm_num
  have hA : (4 * Real.pi * R ^ 2) ^ (3 / 4 : ℝ) = τ * ρ ^ 3 := by
    rw [Real.mul_rpow (by positivity) (by positivity), dfb7_pow_rpow _ hR.le, hτdef, hρ3]
    norm_num
  rw [hZm, hV6, hV2, hA, ← hWdef]
  rw [← hW4, ← hρ2]
  refine ⟨?_, ?_, ?_⟩
  · have e : κ * c * W⁻¹ * (κ * ρ)⁻¹ = c / (W * ρ) := by field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    linarith [key]
  · calc C₂ * W ^ 4 * (k * (ρ ^ 2) ^ 3) * T ^ 3
          = (C₂ * k * W * ρ ^ 3) * (W * ρ * T) ^ 3 := by ring
      _ < (C₂ * k * W * ρ ^ 3) * c ^ 3 := mul_lt_mul_of_pos_left h3 (by positivity)
      _ = C₂ * k * c ^ 3 / σ * W * (σ * ρ ^ 3) := by field_simp
  · calc C₂ * W ^ 4 * (k * (ρ ^ 2) ^ 3) * T ^ 3
          = (C₂ * k * W * ρ ^ 3) * (W * ρ * T) ^ 3 := by ring
      _ < (C₂ * k * W * ρ ^ 3) * c ^ 3 := mul_lt_mul_of_pos_left h3 (by positivity)
      _ = C₂ * k * c ^ 3 / τ * W * (τ * ρ ^ 3) := by field_simp
