-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.eulerDerivation_fraction_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:59:24.437529+00:00
-- url     : https://prove2.me/submissions/04049b67-8b7b-487f-ba51-8a5f917ff47b

import Mathlib
open RatFunc

theorem dpoly (K : Type) [Field K] (d : Derivation K (RatFunc K) (RatFunc K))
    (hdX : d RatFunc.X = RatFunc.X) (p : Polynomial K) :
    d (p : RatFunc K) = RatFunc.X * ((p.derivative : Polynomial K) : RatFunc K) := by
  simp only [RatFunc.coePolynomial_eq_algebraMap]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, mul_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, Derivation.leibniz, Derivation.leibniz_pow, hdX]
    rw [show RatFunc.C a = algebraMap K (RatFunc K) a from rfl, Derivation.map_algebraMap]
    simp only [Polynomial.derivative_C_mul_X_pow, map_mul, map_pow, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X, smul_eq_mul, nsmul_eq_mul, smul_zero, add_zero]
    cases n with
    | zero => simp
    | succ k => simp [pow_succ]; ring

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
  refine ⟨r.num, r.denom, ?_, r.denom_ne_zero, r.isCoprime_num_denom, ?_⟩
  · simp only [RatFunc.coePolynomial_eq_algebraMap]; exact (r.num_div_denom).symm
  · have hq0 : (r.denom : RatFunc K) ≠ 0 := by
      simp only [RatFunc.coePolynomial_eq_algebraMap]
      exact RatFunc.algebraMap_ne_zero r.denom_ne_zero
    have hr : (r.num : RatFunc K) = r * r.denom := by
      have := r.num_div_denom
      simp only [RatFunc.coePolynomial_eq_algebraMap] at hq0 ⊢
      exact ((eq_div_iff hq0).mp this.symm).symm
    have h1 := congrArg d hr
    rw [Derivation.leibniz, dpoly K d hdX, dpoly K d hdX, smul_eq_mul, smul_eq_mul] at h1
    linear_combination (-(r.denom : RatFunc K)) * h1 +
      (RatFunc.X * ((r.denom.derivative : Polynomial K) : RatFunc K)) * hr
