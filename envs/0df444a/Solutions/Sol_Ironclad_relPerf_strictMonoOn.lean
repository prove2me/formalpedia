-- Prove2me | solution 1 for Ironclad.relPerf_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:07:27.165492+00:00
-- url     : https://prove2.me/submissions/5e7dd13e-ef98-46f9-83aa-75e4e38b50ea

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

set_option autoImplicit false

open Ironclad

theorem solution (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) :
    (∀ θ : ℝ, alphaClosed ph 0 Δ θ = ph * (1 - ph) ^ (2 * Δ)) ∧
    (∀ θ : ℝ, relPerf ph q Δ θ (alphaClosed ph q Δ θ) =
      (1 - qH ph q) ^ Δ / (ph * (qh ph q + θ * qH ph q) * (1 - ph) ^ (2 * Δ)) *
        (qh ph q ^ 2 * (1 - ph) ^ (2 * Δ) + qh ph q * qH ph q * (1 - ph) ^ Δ * (1 - qH ph q) ^ Δ +
          θ * ph * qH ph q * (1 - qH ph q) ^ Δ)) ∧
    StrictMonoOn (fun θ : ℝ => relPerf ph q Δ θ (alphaClosed ph q Δ θ)) (Set.Ici 0) := by
  have hph : ph ≠ 0 := hph0.ne'
  have h1 : ∀ θ : ℝ, alphaClosed ph 0 Δ θ = ph * (1 - ph) ^ (2 * Δ) := by
    intro θ
    simp only [alphaClosed, qH, qh, zero_mul, sub_zero, one_pow, one_mul, mul_zero, add_zero]
    field_simp
  have h2 : ∀ θ : ℝ, relPerf ph q Δ θ (alphaClosed ph q Δ θ) =
      (1 - qH ph q) ^ Δ / (ph * (qh ph q + θ * qH ph q) * (1 - ph) ^ (2 * Δ)) *
        (qh ph q ^ 2 * (1 - ph) ^ (2 * Δ) + qh ph q * qH ph q * (1 - ph) ^ Δ * (1 - qH ph q) ^ Δ +
          θ * ph * qH ph q * (1 - qH ph q) ^ Δ) := by
    intro θ
    have hw : qh ph q + θ * qH ph q = ph * (θ * q + 1 - q) := by unfold qh qH; ring
    rw [relPerf, h1, hw, alphaClosed]
    by_cases hw0 : θ * q + 1 - q = 0
    · simp [hw0]
    · field_simp
  refine ⟨h1, h2, ?_⟩
  have hy0 : 0 < qH ph q := mul_pos hq0 hph0
  have hy1 : qH ph q < 1 := by unfold qH; nlinarith
  have hx0 : 0 < qh ph q := mul_pos (by linarith) hph0
  have hrel : qh ph q + qH ph q = ph := by unfold qh qH; ring
  have ha0 : 0 < (1 - ph) ^ Δ := pow_pos (by linarith) Δ
  have ha1 : (1 - ph) ^ Δ < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hb1 : (1 - qH ph q) ^ Δ < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hab : (1 - ph) ^ Δ < (1 - qH ph q) ^ Δ := by
    apply pow_lt_pow_left₀ _ (by linarith) (by omega)
    have : qH ph q < ph := by unfold qH; nlinarith
    linarith
  have hsq : (1 - ph) ^ (2 * Δ) = ((1 - ph) ^ Δ) ^ 2 := by rw [mul_comm, pow_mul]
  intro θ1 hθ1 θ2 hθ2 hlt
  simp only [Set.mem_Ici] at hθ1 hθ2
  simp only [h2, hsq]
  generalize (1 - ph) ^ Δ = a at *
  generalize (1 - qH ph q) ^ Δ = b at *
  generalize qh ph q = x at *
  generalize qH ph q = y at *
  subst hrel
  have hb0 : 0 < b := by linarith
  have hx1 : 0 < x + θ1 * y := by positivity
  have hx2 : 0 < x + θ2 * y := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
  have hK : 0 < (x + y) * b - x * a ^ 2 - y * a * b := by
    have h1' : a ^ 2 < b := by nlinarith
    have := mul_pos hx0 (sub_pos.2 h1')
    have := mul_pos hy0 (mul_pos hb0 (sub_pos.2 ha1))
    nlinarith
  have hpos : 0 < b * (x + y) * a ^ 2 * ((θ2 - θ1) * (x * y * ((x + y) * b - x * a ^ 2 - y * a * b))) := by
    apply mul_pos (by positivity)
    apply mul_pos (by linarith)
    exact mul_pos (by positivity) hK
  nlinarith [hpos]
