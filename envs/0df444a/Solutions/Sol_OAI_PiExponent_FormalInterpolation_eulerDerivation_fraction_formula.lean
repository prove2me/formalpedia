-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eulerDerivation_fraction_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:59:05.763991+00:00
-- url     : https://prove2.me/submissions/534c05cd-c79d-4085-8d03-4975437215b3

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

open RatFunc

theorem S105EF_poly (K : Type) [Field K] [CharZero K]
    (d : Derivation K (RatFunc K) (RatFunc K))
    (hdX : d RatFunc.X = RatFunc.X) (p : Polynomial K) :
    d (p : RatFunc K) = RatFunc.X * ((p.derivative : Polynomial K) : RatFunc K) := by
  simp only [RatFunc.coePolynomial_eq_algebraMap]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.derivative_add]
    simp only [map_add] at *
    rw [hp, hq]; ring
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.derivative_C_mul_X_pow]
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [← RatFunc.algebraMap_eq_C, ← Algebra.smul_def, d.map_smul, Derivation.leibniz_pow, hdX,
      Algebra.smul_def]
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, map_natCast, Nat.cast_add, Nat.cast_one]
      rw [RatFunc.algebraMap_eq_C]
      push_cast
      simp only [map_add, map_one, map_natCast]
      ring

theorem solution
    (K : Type) [Field K] [CharZero K]
    (d : Derivation K (RatFunc K) (RatFunc K))
    (hdX : d RatFunc.X = RatFunc.X)
    (r : RatFunc K) :
    ∃ p q : Polynomial K,
      r = (p : RatFunc K) / (q : RatFunc K) ∧
      q ≠ 0 ∧ IsCoprime p q ∧
      d r * (q : RatFunc K) ^ 2 =
        RatFunc.X *
          (((p.derivative : Polynomial K) : RatFunc K) * (q : RatFunc K) -
            (p : RatFunc K) * ((q.derivative : Polynomial K) : RatFunc K)) := by
  refine ⟨r.num, r.denom, (RatFunc.num_div_denom r).symm, RatFunc.denom_ne_zero r,
    RatFunc.isCoprime_num_denom r, ?_⟩
  have hq : (r.denom : RatFunc K) ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero r)
  have hdr : d r = d (algebraMap _ _ r.num / algebraMap _ _ r.denom) := by
    rw [RatFunc.num_div_denom]
  rw [hdr, Derivation.leibniz_div, ← RatFunc.coePolynomial_eq_algebraMap,
    ← RatFunc.coePolynomial_eq_algebraMap, S105EF_poly K d hdX, S105EF_poly K d hdX]
  simp only [smul_eq_mul]
  field_simp
