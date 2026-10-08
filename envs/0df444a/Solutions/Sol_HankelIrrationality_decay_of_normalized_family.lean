-- Prove2me | solution 1 for HankelIrrationality.decay_of_normalized_family
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-04T14:01:33.532987+00:00
-- url     : https://prove2.me/submissions/53e2959c-780e-4cee-87c2-922385129af8

import Mathlib

open Polynomial Filter Topology

theorem solution (ξ : ℝ) (F : ℕ → ℚ[X]) (m : ℕ → ℚ) (κ A U : ℝ)
    (hκ : 0 < κ) (hAU : A + U < 0) (hm : ∀ n, 0 < m n)
    (hint : ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (m n) * F n)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (m n) ≤ (A + ε) * (κ * (n : ℝ)) ^ 2)
    (hpos : ∀ᶠ n in atTop, 0 < aeval ξ (F n))
    (hreal : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (aeval ξ (F n)) ≤ (U + ε) * (κ * (n : ℝ)) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∃ Q : ℤ[X],
      (∃ c' : ℚ, 0 < c' ∧ Q.map (Int.castRingHom ℚ) = C c' * F n) ∧
      0 < aeval ξ Q ∧ aeval ξ Q < Real.exp (-c * (n : ℝ) ^ 2) := by
  set δ : ℝ := -(A + U) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set c : ℝ := δ * κ ^ 2 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨c, hcpos, ?_⟩
  filter_upwards [hint, hgrowth δ hδpos, hpos, hreal δ hδpos, eventually_ge_atTop 1]
    with n hQ hlogm hFpos hlogF hn1
  obtain ⟨Q, hQ⟩ := hQ
  refine ⟨Q, ⟨m n, hm n, hQ⟩, ?_⟩
  have heval : aeval ξ Q = (m n : ℝ) * aeval ξ (F n) := by
    have h1 : aeval ξ (Q.map (Int.castRingHom ℚ)) = aeval ξ Q := by
      rw [← algebraMap_int_eq, aeval_map_algebraMap]
    rw [← h1, hQ, map_mul, aeval_C]
    rfl
  have hmpos : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hm n
  have hprod : 0 < (m n : ℝ) * aeval ξ (F n) := mul_pos hmpos hFpos
  rw [heval]
  refine ⟨hprod, ?_⟩
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : Real.log ((m n : ℝ) * aeval ξ (F n)) < -c * (n : ℝ) ^ 2 := by
    rw [Real.log_mul hmpos.ne' hFpos.ne']
    have hsq : 0 < (κ * (n : ℝ)) ^ 2 := by positivity
    have : (A + δ) * (κ * (n : ℝ)) ^ 2 + (U + δ) * (κ * (n : ℝ)) ^ 2
        = -2 * c * (n : ℝ) ^ 2 := by rw [hc, hδ]; ring
    have hcn : 0 < c * (n : ℝ) ^ 2 := by positivity
    linarith
  calc (m n : ℝ) * aeval ξ (F n) = Real.exp (Real.log ((m n : ℝ) * aeval ξ (F n))) :=
        (Real.exp_log hprod).symm
    _ < Real.exp (-c * (n : ℝ) ^ 2) := Real.exp_lt_exp.mpr hlog
