-- Prove2me | solution 1 for MarketFreeze.Hetero.eq15LHS_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:46:42.177981+00:00
-- url     : https://prove2.me/submissions/4fa27134-c902-46dd-85ad-8e2244aabf24

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

open Filter

open MarketFreeze.Hetero in
theorem solution (P : Params) (h0 : Standing P) (hXI : P.I < P.X)
    (hlam : 0 < P.lam) (θ : ℝ) (hθ : θ < 1) :
    StrictMonoOn (eq15LHS P θ) (Set.Ici 0) ∧
    eq15LHS P θ 0 = -(P.lam * (P.X - P.I) * ((1 - θ) / 2 + P.ψ)) ∧
    Filter.Tendsto (eq15LHS P θ) Filter.atTop
      (nhds (P.lam * (P.X - P.I) * (1 - θ) / 2)) := by
  have hψ : 0 < P.ψ := h0.2.2.2.2.2.2
  have hK : 0 < P.lam * (P.X - P.I) := mul_pos hlam (by linarith)
  have ha : 0 < (1 - θ) / 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    unfold eq15LHS
    apply mul_lt_mul_of_pos_left _ hK
    have h1 : (x - 1) / (x + 1) < (y - 1) / (y + 1) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have h2 : P.ψ / (y + 1) ^ 2 < P.ψ / (x + 1) ^ 2 := by
      apply div_lt_div_of_pos_left hψ (by positivity)
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 ha]
  · unfold eq15LHS
    norm_num <;> ring
  · have hu : Tendsto (fun n : ℝ => (n + 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    have hlim : Tendsto (fun n : ℝ => P.lam * (P.X - P.I) *
        ((1 - θ) / 2 * (1 - 2 * (n + 1)⁻¹) - P.ψ * ((n + 1)⁻¹) ^ 2)) atTop
        (nhds (P.lam * (P.X - P.I) * ((1 - θ) / 2 * (1 - 2 * 0) - P.ψ * 0 ^ 2))) := by
      apply Tendsto.const_mul
      apply Tendsto.sub
      · apply Tendsto.const_mul
        apply Tendsto.const_sub
        apply Tendsto.const_mul
        exact hu
      · apply Tendsto.const_mul
        exact hu.pow 2
    have hv : P.lam * (P.X - P.I) * ((1 - θ) / 2 * (1 - 2 * 0) - P.ψ * 0 ^ 2)
        = P.lam * (P.X - P.I) * (1 - θ) / 2 := by ring
    rw [hv] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with n hn
    have hn1 : n + 1 ≠ 0 := by positivity
    unfold eq15LHS
    field_simp
    ring
