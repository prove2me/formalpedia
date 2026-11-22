-- Prove2me | solution 1 for MetricSelfDualCompletion.Completion.AGFoundation.degreeEightReciprocalStepConstructor
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:58:24.104464+00:00
-- url     : https://prove2.me/submissions/83189741-ab16-437f-b2d0-1a1d25d24109

import Mathlib
import Definitions.Def_MetricSelfDualCompletion_AG_SourceStepPolynomialData

set_option autoImplicit false
set_option linter.all false

namespace MetricSelfDualCompletion.Completion.AGFoundation

open Polynomial QEC.Coding.AlgebraicGeometry
open scoped WithZero

/-- Algebraic constructor contract for the actual degree-eight reciprocal
source polynomial. No characteristic hypothesis is required. -/
theorem stepPolynomial_contract
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    IsDiscreteValuationRing P.valuationRing ∧
      (StepData.integralPolynomial P x hx).Monic ∧
      (StepData.integralPolynomial P x hx).natDegree = 8 ∧
      (StepData.integralPolynomial P x hx).IsEisensteinAt
        (IsLocalRing.maximalIdeal P.valuationRing) ∧
      (StepData.polynomial P x hx).Monic ∧
      (StepData.polynomial P x hx).natDegree = 8 ∧
      Irreducible (StepData.polynomial P x hx) ∧
      (StepData.polynomial P x hx).Separable := by
  letI : P.valuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    let y := Classical.choose (P.normalized (WithZero.exp (-1 : ℤ)))
    have hy : P.valuation y = WithZero.exp (-1 : ℤ) :=
      Classical.choose_spec (P.normalized (WithZero.exp (-1 : ℤ)))
    refine ⟨y, P.valuation.ne_zero_iff.mp (by rw [hy]; exact WithZero.exp_ne_zero), ?_⟩
    rw [hy, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : IsDiscreteValuationRing P.valuationRing :=
    Valuation.valuationSubring_isDiscreteValuationRing P.valuation
  have hmonic : (StepData.integralPolynomial P x hx).Monic := by
    rw [StepData.integralPolynomial, add_assoc]
    exact Monic.add_of_left (monic_X_pow 8) (by
      calc
        (C (StepData.coefficient P x hx) * X ^ 7 +
            C (StepData.coefficient P x hx)).degree ≤ (7 : WithBot ℕ) := by
          apply degree_add_le_of_degree_le
          · exact degree_C_mul_X_pow_le 7 _
          · exact degree_C_le.trans (by norm_num)
        _ < ((X : Polynomial P.valuationRing) ^ 8).degree := by
          rw [degree_X_pow]
          norm_num)
  have hdegree : (StepData.integralPolynomial P x hx).natDegree = 8 := by
    apply natDegree_eq_of_degree_eq_some
    rw [StepData.integralPolynomial, add_assoc, degree_add_eq_left_of_degree_lt]
    · exact degree_X_pow (R := P.valuationRing) 8
    · calc
        (C (StepData.coefficient P x hx) * X ^ 7 +
            C (StepData.coefficient P x hx)).degree ≤ (7 : WithBot ℕ) := by
          apply degree_add_le_of_degree_le
          · exact degree_C_mul_X_pow_le 7 _
          · exact degree_C_le.trans (by norm_num)
        _ < ((X : Polynomial P.valuationRing) ^ 8).degree := by
          rw [degree_X_pow]
          norm_num
  have htmem : StepData.coefficient P x hx ∈
      IsLocalRing.maximalIdeal P.valuationRing := by
    rw [(StepData.coefficient_spec P x hx).2.1]
    exact Ideal.mem_span_singleton_self _
  have heisenstein : (StepData.integralPolynomial P x hx).IsEisensteinAt
      (IsLocalRing.maximalIdeal P.valuationRing) := by
    apply hmonic.isEisensteinAt_of_mem_of_notMem
    · exact (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).ne_top
    · intro n hn
      rw [hdegree] at hn
      by_cases hn0 : n = 0
      · subst n
        simpa [StepData.integralPolynomial] using htmem
      by_cases hn7 : n = 7
      · subst n
        simpa [StepData.integralPolynomial] using htmem
      · have hn8 : n ≠ 8 := by omega
        simp only [StepData.integralPolynomial, coeff_add, coeff_X_pow,
          Polynomial.coeff_C_mul_X_pow, coeff_C, if_neg hn8,
          if_neg hn7, if_neg hn0, zero_add, Ideal.zero_mem]
    · simpa [StepData.integralPolynomial] using (StepData.coefficient_spec P x hx).2.2
  have hfieldmonic : (StepData.polynomial P x hx).Monic := hmonic.map _
  have hfielddegree : (StepData.polynomial P x hx).natDegree = 8 := by
    rw [StepData.polynomial, hmonic.natDegree_map, hdegree]
  have hirr : Irreducible (StepData.polynomial P x hx) := by
    have hint : Irreducible (StepData.integralPolynomial P x hx) :=
      heisenstein.irreducible (IsLocalRing.maximalIdeal.isMaximal P.valuationRing).isPrime
        hmonic.isPrimitive (by rw [hdegree]; norm_num)
    exact (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
      (K := K) hmonic).mp hint
  have hexplicit : StepData.polynomial P x hx =
      X ^ 8 + C (StepData.rhs x)⁻¹ * X ^ 7 + C (StepData.rhs x)⁻¹ := by
    simp [StepData.polynomial, StepData.integralPolynomial]
  have hderivative : (StepData.polynomial P x hx).derivative ≠ 0 := by
    have hcoeff7 : (StepData.polynomial P x hx).derivative.coeff 7 = (8 : K) := by
      rw [coeff_derivative, hexplicit]
      norm_num
    have hcoeff6 : (StepData.polynomial P x hx).derivative.coeff 6 =
        (StepData.rhs x)⁻¹ * (7 : K) := by
      rw [coeff_derivative, hexplicit]
      norm_num
    intro hzero
    have h8 : (8 : K) = 0 := by
      simpa only [hcoeff7, coeff_zero] using congrArg (fun f : Polynomial K => f.coeff 7) hzero
    have h7 : (7 : K) = -1 := by linear_combination h8
    have ht : (StepData.rhs x)⁻¹ * (7 : K) = 0 := by
      simpa only [hcoeff6, coeff_zero] using congrArg (fun f : Polynomial K => f.coeff 6) hzero
    have ht0 : (StepData.rhs x)⁻¹ = 0 := by simpa [h7] using ht
    exact inv_ne_zero (StepData.rhs_ne_zero P x hx) ht0
  exact ⟨inferInstance, hmonic, hdegree, heisenstein, hfieldmonic, hfielddegree, hirr,
    (Polynomial.separable_iff_derivative_ne_zero hirr).mpr hderivative⟩

end MetricSelfDualCompletion.Completion.AGFoundation

#print axioms MetricSelfDualCompletion.Completion.AGFoundation.stepPolynomial_contract

open MetricSelfDualCompletion.Completion.AGFoundation
theorem solution
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    IsDiscreteValuationRing P.valuationRing ∧
      (StepData.integralPolynomial P x hx).Monic ∧
      (StepData.integralPolynomial P x hx).natDegree = 8 ∧
      (StepData.integralPolynomial P x hx).IsEisensteinAt
        (IsLocalRing.maximalIdeal P.valuationRing) ∧
      (StepData.polynomial P x hx).Monic ∧
      (StepData.polynomial P x hx).natDegree = 8 ∧
      Irreducible (StepData.polynomial P x hx) ∧
      (StepData.polynomial P x hx).Separable :=
  MetricSelfDualCompletion.Completion.AGFoundation.stepPolynomial_contract P x hx

#print axioms solution
