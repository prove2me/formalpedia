-- Prove2me | solution 5 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:33:57.323352+00:00
-- url     : https://prove2.me/submissions/f614856b-e6b8-4b86-9337-85efb9b5eabe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
import Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates

open scoped BigOperators

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < 2*s.re-1 := by linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (‖s‖^2 / (2*s.re-1))
  obtain ⟨c,H,hC⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  let M : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
  change M < 1/(J+1 : ℚ) at hC
  have hc : (M:ℝ) < 1/(J+1:ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr hC
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using ht
  have hh := NymanBeurling.finite_remainder_zero_obstruction s hs hs_one hz c H
  change 2*s.re-1 ≤ (M:ℝ)*‖s‖^2 at hh
  apply (not_lt_of_ge hh)
  calc
    _ ≤ (1/(J+1:ℝ))*‖s‖^2 := mul_le_mul_of_nonneg_right hc.le (sq_nonneg _)
    _ < 2*s.re-1 := by
      rw [one_div,inv_mul_eq_div,div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hpos).mp hJ
      nlinarith
