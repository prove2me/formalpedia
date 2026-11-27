-- Prove2me | solution 1 for MultiNashRepair.controls_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:00:08.930515+00:00
-- url     : https://prove2.me/submissions/554967b9-02e9-4158-a319-abc554d69e90

import Mathlib
import Definitions.Def_MultiNashRepair_Knobs

open MultiNashRepair

set_option maxHeartbeats 2000000 in
theorem solution (f0 u : ℝ) (hf1 : 7 / 12 ≤ f0) (hf2 : f0 ≤ 3 / 5) (hu0 : 0 < u)
    (hu1 : u ≤ 1 / 16) :
    let k : Knobs := ⟨f0, u⟩
    (0 < k.R0 ∧ k.R0 < 1 ∧ 1 < k.Q ∧ k.Q < 2 ∧ 0 < k.au ∧ k.au < 1 ∧ k.L0 < f0 ∧
        k.Q * k.L0 < k.c) ∧
      ∀ H : ℝ, 0 ≤ H → H ≤ k.L0 →
        0 < 1 - k.R0 * (k.Q - 1) ∧ 1 - k.R0 * (k.Q - 1) ≤ deriv k.Su H ∧
          k.Su H ≤ 1 + k.L0 + k.R0 ∧ 1 + k.L0 + k.R0 < 13 / 5 := by
  intro k
  have hf0 : 0 < f0 := by linarith
  have e1 : k.f0 = f0 := rfl
  have e2 : k.u = u := rfl
  have hc : k.c = 1 - u + u ^ 2 / 2 - u ^ 3 := rfl
  have hcpos : 0 < k.c := by rw [hc]; nlinarith
  have hc1 : k.c < 1 := by rw [hc]; nlinarith
  have hw : 0 < 1 + u - u ^ 2 := by nlinarith
  have hv : 0 < 1 - u / 2 + u ^ 2 := by nlinarith
  have hR0 : k.R0 = (1 - f0) * (1 - (1 - f0) * u / 2) / (k.c * f0 * (1 + u - u ^ 2)) := by
    simp only [Knobs.R0, Knobs.rho, Knobs.beta, Knobs.t, Knobs.u0, e1, e2]
    have h1 : (0:ℝ) < 1 + (u - u^2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hQ : k.Q = (1 - u) / (f0 * (1 + u - u ^ 2)) := by
    simp only [Knobs.Q, Knobs.nu, Knobs.beta, Knobs.t, Knobs.u0, e1, e2]
    have h1 : (0:ℝ) < 1 + (u - u^2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hL0 : k.L0 = k.c * f0 / (1 - u / 2 + u ^ 2) := by
    simp only [Knobs.L0, Knobs.t, e1, e2]
    rw [hc]
    have : (1 - (1 - u + u ^ 2 / 2 - u ^ 3)) = u * (1 - u / 2 + u ^ 2) := by ring
    rw [this]
    have : u ≠ 0 := hu0.ne'
    field_simp
  have hden : 0 < k.c * f0 * (1 + u - u ^ 2) := by positivity
  have hR0pos : 0 < k.R0 := by
    rw [hR0]; apply div_pos _ hden
    apply mul_pos (by linarith); nlinarith
  have hR0lt : k.R0 < 1 := by
    rw [hR0, div_lt_one hden, hc]
    nlinarith [mul_pos hu0 hu0, mul_pos (mul_pos hu0 hu0) hu0, mul_pos hf0 hu0,
      mul_pos (mul_pos hf0 hu0) hu0]
  have hfw : 0 < f0 * (1 + u - u ^ 2) := by positivity
  have hQ1 : 1 < k.Q := by
    rw [hQ, one_lt_div hfw]; nlinarith
  have hQ2 : k.Q < 2 := by
    rw [hQ, div_lt_iff₀ hfw]; nlinarith
  have hL0f : k.L0 < f0 := by
    rw [hL0, div_lt_iff₀ hv, hc]; nlinarith [mul_pos hf0 hu0, mul_pos (mul_pos hf0 hu0) hu0]
  have hL0pos : 0 < k.L0 := by rw [hL0]; positivity
  have hQL0 : k.Q * k.L0 < k.c := by
    rw [hQ, hL0]
    rw [show (1 - u) / (f0 * (1 + u - u ^ 2)) * (k.c * f0 / (1 - u / 2 + u ^ 2))
        = k.c * ((1 - u) / ((1 + u - u ^ 2) * (1 - u / 2 + u ^ 2))) by field_simp]
    have : (1 - u) / ((1 + u - u ^ 2) * (1 - u / 2 + u ^ 2)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [mul_pos hu0 hu0, mul_pos (mul_pos hu0 hu0) hu0]
    nlinarith
  have hau : k.au = k.R0 * (k.Q - 1) := rfl
  have hau0 : 0 < k.au := by rw [hau]; exact mul_pos hR0pos (by linarith)
  have hau1 : k.au < 1 := by
    rw [hau]
    calc k.R0 * (k.Q - 1) < 1 * 1 := by
          apply mul_lt_mul'' hR0lt (by linarith) hR0pos.le (by linarith)
      _ = 1 := by ring
  refine ⟨⟨hR0pos, hR0lt, hQ1, hQ2, hau0, hau1, hL0f, hQL0⟩, ?_⟩
  intro H hH0 hHL
  have hQH : 0 < 1 + k.Q * H := by nlinarith
  have hderiv : HasDerivAt k.Su (1 + k.R0 * (1 - k.Q) / (1 + k.Q * H) ^ 2) H := by
    have h1 : HasDerivAt (fun H : ℝ => 1 + H) 1 H := (hasDerivAt_id H).const_add 1
    have h2 : HasDerivAt (fun H : ℝ => k.R0 * (1 + H)) (k.R0 * 1) H := h1.const_mul k.R0
    have h3 : HasDerivAt (fun H : ℝ => 1 + k.Q * H) (k.Q * 1) H :=
      ((hasDerivAt_id H).const_mul k.Q).const_add 1
    have h4 := h2.div h3 hQH.ne'
    have h5 := h1.add h4
    have h6 : HasDerivAt k.Su
        (1 + (k.R0 * 1 * (1 + k.Q * H) - k.R0 * (1 + H) * (k.Q * 1)) / (1 + k.Q * H) ^ 2) H := h5
    exact h6.congr_deriv (by ring)
  refine ⟨by linarith, ?_, ?_, by linarith⟩
  · rw [hderiv.deriv]
    have hQH0 : 0 ≤ k.Q * H := mul_nonneg (by linarith) hH0
    have hsq : 1 ≤ (1 + k.Q * H) ^ 2 := by nlinarith
    have hnn : 0 ≤ k.R0 * (k.Q - 1) := mul_nonneg hR0pos.le (by linarith)
    have := div_le_self hnn hsq
    have e : k.R0 * (1 - k.Q) / (1 + k.Q * H) ^ 2 = -(k.R0 * (k.Q - 1) / (1 + k.Q * H) ^ 2) := by
      ring
    rw [e]; linarith
  · simp only [Knobs.Su, Knobs.Cu]
    have : k.R0 * (1 + H) / (1 + k.Q * H) ≤ k.R0 := by
      rw [div_le_iff₀ hQH]
      have h1 := mul_nonneg (sub_nonneg.mpr hQ1.le) hH0
      have h2 : 1 + H ≤ 1 + k.Q * H := by linarith
      exact mul_le_mul_of_nonneg_left h2 hR0pos.le
    linarith
