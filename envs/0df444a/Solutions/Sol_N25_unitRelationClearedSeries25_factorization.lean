-- Prove2me | solution 1 for N25.unitRelationClearedSeries25_factorization
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:05.152911+00:00
-- url     : https://prove2.me/submissions/9de3675a-4f1b-4e59-be5f-229de4d40753

import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitRelationCertificate

set_option autoImplicit false

open scoped BigOperators

namespace N25

private theorem pair_constant (i : Fin 5) :
    PowerSeries.constantCoeff (unitPairSeries25 i) = 1 := by
  have residue (g : ℕ) (hg : 0 < g) (hg25 : g < 25) :
      PowerSeries.constantCoeff (etaResidueSeries25 g) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp only [etaResidueSeries25, PowerSeries.coeff_mk, zero_add,
      Finset.range_one, Finset.prod_singleton, mul_zero, zero_add, mul_one]
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    simp [map_mul, map_sub, map_pow, Nat.ne_of_gt hg,
      Nat.ne_of_gt (Nat.sub_pos_of_lt hg25)]
  have bounds : ∀ i : Fin 5,
      0 < (unitResidues25 i).1 ∧ (unitResidues25 i).1 < 25 ∧
      0 < (unitResidues25 i).2 ∧ (unitResidues25 i).2 < 25 := by
    intro i
    fin_cases i <;> norm_num [unitResidues25]
  rw [unitPairSeries25, map_mul,
    residue _ (bounds i).1 (bounds i).2.1,
    residue _ (bounds i).2.2.1 (bounds i).2.2.2, one_mul]

private theorem cleared_factorization {A : Type*} [CommRing A]
    (q d p r s ir js : A) (hr : r*ir=1) (hs : s*js=1) :
    clearedUnitRelation25 (q^3*d) (q^4*d*p*ir) (q^2*d*r*js) * (r^5*s^4) =
      q^29*d^11 * unitRelationNumerator25 q p r s := by
  calc
    _ = q^29*d^11 *
        (q^8*p^4*s^4*r*(r*ir)^4 - q^9*p^6*s^3*(r*ir)^6*(s*js) +
          q^5*p^3*s^2*r^4*(r*ir)^3*(s*js)^2 -
          q^7*p^5*s^2*r^2*(r*ir)^5*(s*js)^2 -
          2*q^8*p^6*s^2*r*(r*ir)^6*(s*js)^2 -
          q^5*p^4*s*r^4*(r*ir)^4*(s*js)^3 -
          q^6*p^5*s*r^3*(r*ir)^5*(s*js)^3 -
          2*q^7*p^6*s*r^2*(r*ir)^6*(s*js)^3 +
          q^7*p^7*r^2*(r*ir)^7*(s*js)^4) := by
      unfold clearedUnitRelation25
      ring
    _ = _ := by simp [hr, hs, unitRelationNumerator25]

/-- Clearing the two residue-pair inverses reduces the frozen series to a
finite polynomial expression in three unshifted Euler products. -/
theorem _root_.solution :
    unitRelationClearedSeries25 * ((unitPairSeries25 1)^5 * (unitPairSeries25 2)^4) =
      PowerSeries.X^29 * (ModularCurve.dedekindEtaUnit^3)^11 *
        unitRelationNumerator25 PowerSeries.X
          (unitPairSeries25 0) (unitPairSeries25 1) (unitPairSeries25 2) ∧
      IsUnit ((unitPairSeries25 1)^5 * (unitPairSeries25 2)^4) := by
  constructor
  · have hr := PowerSeries.mul_invOfUnit (unitPairSeries25 1) (1 : ℤˣ) (pair_constant 1)
    have hs := PowerSeries.mul_invOfUnit (unitPairSeries25 2) (1 : ℤˣ) (pair_constant 2)
    convert cleared_factorization PowerSeries.X (ModularCurve.dedekindEtaUnit^3)
      (unitPairSeries25 0) (unitPairSeries25 1) (unitPairSeries25 2)
      ((unitPairSeries25 1).invOfUnit (1 : ℤˣ))
      ((unitPairSeries25 2).invOfUnit (1 : ℤˣ)) hr hs using 1
    simp [unitRelationClearedSeries25, unitDenominatorSeries25,
      unitNumeratorSeries25, unitQOrder25, mul_pow]
  · apply IsUnit.mul
    · apply IsUnit.pow
      exact PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [pair_constant]; exact isUnit_one)
    · apply IsUnit.pow
      exact PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [pair_constant]; exact isUnit_one)

end N25
