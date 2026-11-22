-- Prove2me | solution 1 for MetricSelfDualCompletion.Completion.AGFoundation.inverseSimplePoleUniformizer
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:40:49.76129+00:00
-- url     : https://prove2.me/submissions/83096850-723d-4d21-b2ab-d34af7b2ad74

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace

set_option autoImplicit false
set_option linter.all false

namespace MetricSelfDualCompletion.Completion.AGFoundation

open QEC.Coding.AlgebraicGeometry
open scoped WithZero

/-- The reciprocal of any normalized simple pole is an exact uniformizer.
The valuation ring and maximal ideal are the actual Mathlib constructions. -/
theorem inversePole_contract
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    ∃ hmem : x⁻¹ ∈ P.valuationRing,
      let t : P.valuationRing := ⟨x⁻¹, hmem⟩
      t ≠ 0 ∧
        IsLocalRing.maximalIdeal P.valuationRing = Ideal.span {t} ∧
        t ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    simp [GlobalPlace.order] at hx
  have hlog : WithZero.log (P.valuation x) = 1 := by
    change -WithZero.log (P.valuation x) = -1 at hx
    omega
  have hinvlog : WithZero.log (P.valuation x⁻¹) = -1 := by
    rw [(P.valuation).map_inv x, WithZero.log_inv, hlog]
  have hinvval : P.valuation x⁻¹ = WithZero.exp (-1 : ℤ) := by
    calc
      P.valuation x⁻¹ = WithZero.exp (WithZero.log (P.valuation x⁻¹)) :=
        (WithZero.exp_log (P.valuation.ne_zero_iff.mpr (inv_ne_zero hx0))).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hinvlog]
  have hmem : x⁻¹ ∈ P.valuationRing := by
    apply (P.valuation.mem_valuationSubring_iff x⁻¹).mpr
    rw [hinvval, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  let t : P.valuationRing := ⟨x⁻¹, hmem⟩
  have ht0 : t ≠ 0 := by
    intro hzero
    exact inv_ne_zero hx0 (congrArg (fun z : P.valuationRing => (z : K)) hzero)
  letI : P.valuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
    rw [hinvval, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  letI : IsCyclic (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup
    (MonoidWithZeroHom.ofClass P.valuation)) := inferInstance
  letI : P.valuation.IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' P.valuation
  have hmax : IsLocalRing.maximalIdeal P.valuationRing = Ideal.span {t} := by
    apply Valuation.IsUniformizer.is_generator
    change P.valuation x⁻¹ =
      ((Valuation.IsRankOneDiscrete.generator P.valuation :
        (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))
    rw [hinvval]
    simpa using congrArg
      (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ)))
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v := P.valuation) P.normalized).symm
  have htmem : t ∈ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [hmax]
    exact Ideal.mem_span_singleton_self t
  have hnot : t ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 := by
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have hone : (1 : P.valuationRing) = t * c := by
      apply mul_left_cancel₀ ht0
      calc
        t * 1 = t := mul_one _
        _ = t ^ 2 * c := hc
        _ = t * (t * c) := by rw [pow_two, mul_assoc]
    have hunit : IsUnit t := isUnit_iff_exists_inv.mpr ⟨c, hone.symm⟩
    have hnotunit : ¬IsUnit t := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using htmem
    exact hnotunit hunit
  exact ⟨hmem, ht0, hmax, hnot⟩

end MetricSelfDualCompletion.Completion.AGFoundation

#print axioms MetricSelfDualCompletion.Completion.AGFoundation.inversePole_contract

theorem solution
    {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    (P : QEC.Coding.AlgebraicGeometry.GlobalPlace k K) (x : K) (hx : P.order x = -1) :
    ∃ hmem : x⁻¹ ∈ P.valuationRing,
      let t : P.valuationRing := ⟨x⁻¹, hmem⟩
      t ≠ 0 ∧
        IsLocalRing.maximalIdeal P.valuationRing = Ideal.span {t} ∧
        t ∉ (IsLocalRing.maximalIdeal P.valuationRing) ^ 2 :=
  MetricSelfDualCompletion.Completion.AGFoundation.inversePole_contract P x hx

#print axioms solution
