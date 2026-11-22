-- Prove2me | solution 1 for MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.exists_quadratic_polynomial_factors_of_card8
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T11:15:56.330683+00:00
-- url     : https://prove2.me/submissions/c1d198dd-e9e2-469e-8bee-feb0b3bf6af0

import Mathlib

open Polynomial

namespace MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial

noncomputable section

abbrev F8 : Type := GaloisField 2 3
instance f8Fintype : Fintype F8 := Fintype.ofFinite F8

theorem f8_card : Fintype.card F8 = 8 := by
  rw [Fintype.card_eq_nat_card]
  simpa using (GaloisField.card 2 3 (by norm_num : (3 : ℕ) ≠ 0))

def cubic : F8[X] := X ^ 3 + X + 1

theorem cubic_dvd : cubic ∣ (X ^ 8 - X : F8[X]) := by
  refine ⟨X * (X + 1) * (X ^ 3 + X ^ 2 + 1), ?_⟩
  unfold cubic
  ring_nf
  have h2 : (2 : F8[X]) = 0 := CharP.cast_eq_zero F8[X] 2
  have h4 : (4 : F8[X]) = 0 := by linear_combination 2 * h2
  simp only [h2, h4, mul_zero, zero_add, add_zero, CharTwo.neg_eq]

theorem cubic_splits : cubic.Splits := by
  have hs := FiniteField.splits_X_pow_card_sub_X (K := F8) 2
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, f8_card] at hs
  apply hs.of_dvd ?_ cubic_dvd
  intro h
  have hc := congrArg (fun p : F8[X] => p.coeff 8) h
  norm_num [Polynomial.coeff_X] at hc

theorem cubic_natDegree : cubic.natDegree = 3 := by
  unfold cubic
  compute_degree!

theorem exists_cubic_root : ∃ c : F8, c ^ 3 + c + 1 = 0 := by
  obtain ⟨c, hc⟩ := cubic_splits.exists_eval_eq_zero
    (degree_ne_of_natDegree_ne (by rw [cubic_natDegree]; norm_num))
  exact ⟨c, by simpa [cubic] using hc⟩

def coefficient : F8 := Classical.choose exists_cubic_root

theorem coefficient_equation : coefficient ^ 3 + coefficient + 1 = 0 :=
  Classical.choose_spec exists_cubic_root

theorem coefficient_ne_zero : coefficient ≠ 0 := by
  intro h
  have he := coefficient_equation
  rw [h] at he
  norm_num at he

theorem coefficient_ne_one : coefficient ≠ 1 := by
  intro h
  have he := coefficient_equation
  rw [h] at he
  exact one_ne_zero (by simpa only [one_pow, CharTwo.add_self_eq_zero, zero_add] using he)

def secondCoefficient : F8 := 1 + coefficient ^ 2

theorem secondCoefficient_ne_zero : secondCoefficient ≠ 0 := by
  intro h
  have he : (coefficient + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, one_pow]
    simpa only [secondCoefficient, add_comm] using h
  have hc : coefficient + 1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp he
  have htwo : (2 : F8) = 0 := CharP.cast_eq_zero F8 2
  apply coefficient_ne_one
  linear_combination hc - htwo

def firstPolynomial : F8[X] := X ^ 2 + X
def secondPolynomial : F8[X] := firstPolynomial ^ 2 + C coefficient * firstPolynomial
def thirdPolynomial : F8[X] := secondPolynomial ^ 2 + C secondCoefficient * secondPolynomial

/-- The degree-eight Artin--Schreier polynomial factors into three genuine
quadratic linearized maps with nonzero constant coefficients. Repeating
the same map `T^2+T` three times would leave mixed terms; the two selected
F8 coefficients are essential. -/
theorem three_quadratic_factorization : thirdPolynomial = X ^ 8 + X := by
  have hcp : (C coefficient : F8[X]) ^ 3 + C coefficient + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg (C : F8 →+* F8[X]) coefficient_equation
  simp only [thirdPolynomial, secondPolynomial, firstPolynomial,
    secondCoefficient, map_add, map_pow, map_one]
  have h2 : (2 : F8[X]) = 0 := CharP.cast_eq_zero F8[X] 2
  have h4 : (4 : F8[X]) = 0 := by linear_combination 2 * h2
  have h6 : (6 : F8[X]) = 0 := by linear_combination 3 * h2
  linear_combination (norm := skip) (X ^ 2 + X) * hcp
  ring_nf
  simp only [h2, h4, h6, mul_zero, zero_add, add_zero, neg_zero]

theorem three_quadratic_evaluate {K : Type*} [CommRing K] [Algebra F8 K] (y : K) :
    ((y ^ 2 + y) ^ 2 + algebraMap F8 K coefficient * (y ^ 2 + y)) ^ 2 +
      algebraMap F8 K secondCoefficient *
        ((y ^ 2 + y) ^ 2 + algebraMap F8 K coefficient * (y ^ 2 + y)) = y ^ 8 + y := by
  have h := congrArg (Polynomial.aeval y) three_quadratic_factorization
  simpa only [thirdPolynomial, secondPolynomial, firstPolynomial, map_add, map_pow,
    map_mul, Polynomial.aeval_C, Polynomial.aeval_X] using h

theorem exists_nonzero_quadratic_coefficients : ∃ c d : F8,
    c ≠ 0 ∧ d ≠ 0 ∧ ∀ y : F8,
      ((y ^ 2 + y) ^ 2 + c * (y ^ 2 + y)) ^ 2 +
        d * ((y ^ 2 + y) ^ 2 + c * (y ^ 2 + y)) = y ^ 8 + y := by
  refine ⟨coefficient, secondCoefficient, coefficient_ne_zero, secondCoefficient_ne_zero, ?_⟩
  intro y
  simpa using three_quadratic_evaluate y

/-- Every eight-element binary field admits the required three quadratic
linearized factors. This asserts existence of both nonzero coefficients. -/
theorem exists_quadratic_factors_of_card8 (E : Type*) [Field E] [Fintype E]
    [Algebra (ZMod 2) E] (hcard : Fintype.card E = 8) :
    ∃ c d : E, c ≠ 0 ∧ d ≠ 0 ∧ ∀ y : E,
      ((y ^ 2 + y) ^ 2 + c * (y ^ 2 + y)) ^ 2 +
        d * ((y ^ 2 + y) ^ 2 + c * (y ^ 2 + y)) = y ^ 8 + y := by
  let e : F8 ≃ₐ[ZMod 2] E := FiniteField.algEquivOfCardEq 2 (f8_card.trans hcard.symm)
  obtain ⟨c, d, hc, hd, heq⟩ := exists_nonzero_quadratic_coefficients
  refine ⟨e c, e d, ?_, ?_, ?_⟩
  · simpa only [map_zero] using e.injective.ne hc
  · simpa only [map_zero] using e.injective.ne hd
  · intro y
    simpa only [map_add, map_pow, map_mul, e.apply_symm_apply] using
      congrArg e (heq (e.symm y))

theorem exists_quadratic_polynomial_factors_of_card8 (E : Type*) [Field E] [Fintype E]
    [Algebra (ZMod 2) E] (hcard : Fintype.card E = 8) :
    ∃ c d : E, c ≠ 0 ∧ d ≠ 0 ∧
      (((X ^ 2 + X : E[X]) ^ 2 + C c * (X ^ 2 + X)) ^ 2 +
        C d * ((X ^ 2 + X) ^ 2 + C c * (X ^ 2 + X))) = X ^ 8 + X := by
  let e : F8 ≃ₐ[ZMod 2] E := FiniteField.algEquivOfCardEq 2 (f8_card.trans hcard.symm)
  refine ⟨e coefficient, e secondCoefficient, ?_, ?_, ?_⟩
  · simpa only [map_zero] using e.injective.ne coefficient_ne_zero
  · simpa only [map_zero] using e.injective.ne secondCoefficient_ne_zero
  · have h := congrArg (Polynomial.map e.toRingHom) three_quadratic_factorization
    simpa [thirdPolynomial, secondPolynomial, firstPolynomial] using h

end
end MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial

open MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial
theorem solution (E : Type*) [Field E] [Fintype E]
    [Algebra (ZMod 2) E] (hcard : Fintype.card E = 8) :
    ∃ c d : E, c ≠ 0 ∧ d ≠ 0 ∧
      (((X ^ 2 + X : E[X]) ^ 2 + C c * (X ^ 2 + X)) ^ 2 +
        C d * ((X ^ 2 + X) ^ 2 + C c * (X ^ 2 + X))) = X ^ 8 + X := by
  exact exists_quadratic_polynomial_factors_of_card8 E hcard

#print axioms MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.cubic_splits

#print axioms MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.exists_cubic_root

#print axioms MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.coefficient_ne_zero

#print axioms MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.secondCoefficient_ne_zero

#print axioms MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.three_quadratic_factorization

#print axioms MetricSelfDualCompletion.Completion.AGProof.RefinementPolynomial.exists_quadratic_polynomial_factors_of_card8

#print axioms solution
