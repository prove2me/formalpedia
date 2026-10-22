-- Prove2me | solution 1 for InfoRegimes.MarketEq.mean_variance_demand
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:21:42.839813+00:00
-- url     : https://prove2.me/submissions/24e370c3-95c5-4284-82be-1f8e8af633f3

import Mathlib

theorem solution (γ qD qN q : ℝ) (hγ : 0 < γ) (hqD : 0 < qD) :
    IsMaxOn (fun x : ℝ => x * qN - γ / 2 * x ^ 2 * qD) Set.univ q ↔ q = qN / (γ * qD) := by
  have hc : 0 < γ * qD := mul_pos hγ hqD
  set s := qN / (γ * qD) with hs
  have hqN : qN = s * (γ * qD) := by rw [hs]; field_simp
  have key : ∀ x y : ℝ, (y * qN - γ / 2 * y ^ 2 * qD) - (x * qN - γ / 2 * x ^ 2 * qD) =
      γ * qD / 2 * ((x - s) ^ 2 - (y - s) ^ 2) := by
    intro x y; rw [hqN]; ring
  constructor
  · intro h
    have h1 := isMaxOn_iff.1 h s (Set.mem_univ _)
    have := key s q
    have hsq : (q - s) ^ 2 ≤ 0 := by
      have : 0 ≤ γ * qD / 2 * ((s - s) ^ 2 - (q - s) ^ 2) := by
        rw [← key]; linarith
      have hc2 : 0 < γ * qD / 2 := by positivity
      nlinarith
    have : (q - s) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    linarith
  · rintro rfl
    rw [isMaxOn_iff]
    intro x _
    have := key x s
    have : 0 ≤ γ * qD / 2 * ((x - s) ^ 2 - (s - s) ^ 2) := by
      have hc2 : 0 < γ * qD / 2 := by positivity
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
      positivity

    linarith
