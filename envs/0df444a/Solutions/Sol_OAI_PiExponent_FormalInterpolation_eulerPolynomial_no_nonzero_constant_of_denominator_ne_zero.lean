-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eulerPolynomial_no_nonzero_constant_of_denominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:56:27.845421+00:00
-- url     : https://prove2.me/submissions/10fcc90a-380f-4bbc-8ed4-24d14e06c396

import Mathlib.FieldTheory.RatFunc.AsPolynomial

open Polynomial

theorem pe_poly
    (K : Type) [Field K] [CharZero K]
    (p q : Polynomial K) (hq : q ≠ 0) (hcop : IsCoprime p q)
    (c : K) (hc : c ≠ 0)
    (hidentity : Polynomial.C c * q ^ 2 =
      Polynomial.X * (p.derivative * q - p * q.derivative)) :
    False := by
  have h0 : q.eval 0 = 0 := by
    have := congrArg (Polynomial.eval 0) hidentity
    simp at this
    rcases this with h | h
    · exact absurd h hc
    · exact h
  obtain ⟨u, hqu, hu⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0
  have hpos : 0 < q.rootMultiplicity 0 := (Polynomial.rootMultiplicity_pos hq).2 h0
  obtain ⟨j, hj⟩ : ∃ j, q.rootMultiplicity 0 = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hj, map_zero, sub_zero] at hqu
  have hu0 : u.eval 0 ≠ 0 := by
    intro h; apply hu
    rw [map_zero, sub_zero]; exact Polynomial.X_dvd_iff.2 (by simpa [Polynomial.coeff_zero_eq_eval_zero] using h)
  have hp0 : p.eval 0 ≠ 0 := by
    intro h
    have hXp : Polynomial.X ∣ p := Polynomial.X_dvd_iff.2 (by simpa [Polynomial.coeff_zero_eq_eval_zero] using h)
    have hXq : Polynomial.X ∣ q := ⟨Polynomial.X ^ j * u, by rw [hqu]; ring⟩
    have := hcop.isUnit_of_dvd' hXp hXq
    exact Polynomial.not_isUnit_X this
  have hd : q.derivative = ((j : K[X]) + 1) * X ^ j * u + X ^ (j + 1) * u.derivative := by
    rw [hqu, Polynomial.derivative_mul, Polynomial.derivative_X_pow]; simp
  rw [hd, hqu] at hidentity
  have key : X ^ (j + 1) * (C c * X ^ (j + 1) * u ^ 2) =
      X ^ (j + 1) * (X * derivative p * u - ((j : K[X]) + 1) * p * u - X * p * derivative u) := by
    rw [← sub_eq_zero] at hidentity ⊢
    rw [← hidentity]; ring
  have key2 := mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) key
  have := congrArg (Polynomial.eval 0) key2
  simp at this
  rcases this with (h | h) | h
  · exact absurd (by exact_mod_cast h : (j : ℕ) + 1 = 0) (Nat.succ_ne_zero j)
  · exact hp0 h
  · exact hu0 h

open RatFunc in
theorem solution
    (K : Type) [Field K] [CharZero K]
    (p q : Polynomial K) (hq : q ≠ 0) (hcop : IsCoprime p q)
    (c : K) (hc : c ≠ 0)
    (hidentity : algebraMap K (RatFunc K) c * (q : RatFunc K) ^ 2 =
      RatFunc.X *
        (((p.derivative : Polynomial K) : RatFunc K) * (q : RatFunc K) -
          (p : RatFunc K) * ((q.derivative : Polynomial K) : RatFunc K))) :
    False := by
  refine pe_poly K p q hq hcop c hc ?_
  apply RatFunc.algebraMap_injective K
  simp only [map_mul, map_sub, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [← RatFunc.algebraMap_eq_C]
  exact hidentity
