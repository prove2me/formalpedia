-- Prove2me | solution 1 for LamLitt.polynomial_of_integrality_of_entire
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T23:26:21.771884+00:00
-- url     : https://prove2.me/submissions/ec45ceae-c2f5-4ed1-84f5-0c4e9db6a8a2

import Definitions.Def_LamLitt_Defs
import Theorems.Thm_LamLitt_coeff_denominator_bound_of_integrality
import Mathlib

namespace LamLittAuxP

/-- An integer whose image in `ℚ` has absolute value `< 1` is zero. -/
lemma int_eq_zero_of_abs_cast_lt_one (m : ℤ) (h : |(m : ℚ)| < 1) : m = 0 := by
  have h' : |m| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp h'

/-- Key estimate: a rational sequence with geometrically bounded denominators
(`M^(k+1) * a k ∈ ℤ`) and with `|a k| * (2M)^k` bounded is eventually zero. -/
lemma eventually_zero_of_bounds (a : ℕ → ℚ) (M : ℕ) (hM : 0 < M)
    (hint : ∀ k : ℕ, ∃ m : ℤ, (M : ℚ) ^ (k + 1) * a k = (m : ℚ))
    (C : ℚ) (hC : ∀ k : ℕ, |a k| * (((2 * M : ℕ) : ℚ)) ^ k ≤ C) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → a k = 0 := by
  have hMq : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((M : ℚ) * C) (one_lt_two : (1 : ℚ) < 2)
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨m, hm⟩ := hint k
  have h2k : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  have hKk : (2 : ℚ) ^ K ≤ (2 : ℚ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  -- `|m| * 2^k = M * (|a k| * (2M)^k) ≤ M * C < 2^K ≤ 2^k`
  have habs : |(m : ℚ)| * (2 : ℚ) ^ k = (M : ℚ) * (|a k| * (((2 * M : ℕ) : ℚ)) ^ k) := by
    rw [← hm, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < (M : ℚ) ^ (k + 1))]
    push_cast
    rw [mul_pow]
    ring
  have hle : |(m : ℚ)| * (2 : ℚ) ^ k ≤ (M : ℚ) * C := by
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hC k) hMq.le
  have hlt : |(m : ℚ)| * (2 : ℚ) ^ k < 1 * (2 : ℚ) ^ k := by
    rw [one_mul]
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hK hKk)
  have hm1 : |(m : ℚ)| < 1 := lt_of_mul_lt_mul_right hlt h2k.le
  have hm0 : m = 0 := int_eq_zero_of_abs_cast_lt_one m hm1
  rw [hm0, Int.cast_zero] at hm
  rcases mul_eq_zero.mp hm with h | h
  · exact absurd h (pow_ne_zero _ hMq.ne')
  · exact h

/-- A power series whose coefficients vanish from index `K` on is the polynomial `trunc K f`. -/
lemma eq_coe_trunc_of_eventually_zero (f : PowerSeries ℚ) (K : ℕ)
    (h : ∀ k : ℕ, K ≤ k → PowerSeries.coeff k f = 0) :
    f = ((PowerSeries.trunc K f : Polynomial ℚ) : PowerSeries ℚ) := by
  ext k
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hk
  · rfl
  · exact h k (not_lt.mp hk)

end LamLittAuxP

open LamLitt PowerSeries in
theorem solution {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N)
    (hentire : ∀ R : ℕ, ∃ C : ℚ, ∀ k : ℕ, |PowerSeries.coeff k f| * (R : ℚ) ^ k ≤ C) :
    ∃ P : Polynomial ℚ, f = (P : PowerSeries ℚ) := by
  obtain ⟨M, hM, hint⟩ := LamLitt.coeff_denominator_bound_of_integrality f g hODE N hN
  obtain ⟨C, hC⟩ := hentire (2 * M)
  obtain ⟨K, hK⟩ := LamLittAuxP.eventually_zero_of_bounds
    (fun k => PowerSeries.coeff k f) M hM hint C hC
  exact ⟨PowerSeries.trunc K f, LamLittAuxP.eq_coe_trunc_of_eventually_zero f K hK⟩
