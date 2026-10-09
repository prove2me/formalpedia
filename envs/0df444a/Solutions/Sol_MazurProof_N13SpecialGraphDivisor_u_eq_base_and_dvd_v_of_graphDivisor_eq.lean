-- Prove2me | solution 1 for MazurProof.N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:34:41.107876+00:00
-- url     : https://prove2.me/submissions/a46647f4-1d80-43af-96b5-c99eaf24e35f

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialGraphDivisor =====
section
/-!
# Degree-two Mumford graphs as effective divisors on the N13 special fibre

A monic quadratic generalized Mumford graph on the good characteristic-two
model splits over `F₂`.  Indeed, an irreducible quadratic would produce an
affine point over its quadratic root field, while the structural Frobenius
classification forces that root back into `F₂`.

The two roots, with their graph values, therefore define an effective
degree-two divisor.  If that divisor is the selected nonspecial base divisor,
its two distinct points force `u = X² + X` and `u ∣ v`; hence its graph ideal
is literally the fixed special ideal.  No finite table or representative
enumeration is used.
-/
open Polynomial
open scoped Sym2
namespace MazurProof.N13SpecialGraphDivisor
noncomputable section
open MazurProof.N13GoodCoordinateRingTwo
attribute [local instance] MazurProof.N13SpecialGraphDivisor.instFactPrimeOfNatNat_fLT
theorem zero_one_roots_and_values_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    D.u.IsRoot 0 ∧ D.u.IsRoot 1 ∧
      D.v.eval 0 = 0 ∧ D.v.eval 1 = 0 := by
  have hp00 :
      N13AbelChartBase.p00 ∈ graphDivisor D hdeg := by
    rw [hgraph]
    exact Sym2.mem_mk_left _ _
  have hp10 :
      N13AbelChartBase.p10 ∈ graphDivisor D hdeg := by
    rw [hgraph]
    exact Sym2.mem_mk_right _ _
  rw [graphDivisor, Sym2.mem_pmap_iff] at hp00 hp10
  obtain ⟨a, ha, hpa⟩ := hp00
  obtain ⟨b, hb, hpb⟩ := hp10
  have hca := congrArg N13AbelFiberTwoModel.curvePointEquiv hpa
  have hcb := congrArg N13AbelFiberTwoModel.curvePointEquiv hpb
  have ha0 : a = 0 := by
    symm
    simpa [N13AbelChartBase.p00, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.fst hca
  have hva0 : D.v.eval a = 0 := by
    symm
    simpa [N13AbelChartBase.p00, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.snd hca
  have hb1 : b = 1 := by
    symm
    simpa [N13AbelChartBase.p10, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.fst hcb
  have hvb0 : D.v.eval b = 0 := by
    symm
    simpa [N13AbelChartBase.p10, rootPoint,
      N13AbelFiberTwoModel.curvePointEquiv] using congrArg Prod.snd hcb
  subst a
  subst b
  exact
    ⟨(mem_rootPair_iff_isRoot D hdeg 0).mp ha,
      (mem_rootPair_iff_isRoot D hdeg 1).mp hb,
      hva0, hvb0⟩
theorem u_eq_base_and_dvd_v_of_graphDivisor_eq
    (D : SemiMumford) (hdeg : D.u.natDegree = 2)
    (hgraph :
      graphDivisor D hdeg =
        N13AbelChartBase.specialBaseDivisor) :
    D.u = (X ^ 2 + X : K[X]) ∧ D.u ∣ D.v := by
  obtain ⟨hu0, hu1, hv0, hv1⟩ :=
    zero_one_roots_and_values_of_graphDivisor_eq D hdeg hgraph
  have htwo : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  have hunit : IsUnit ((0 : K) - 1) := by
    have hnegOne : (-1 : K) = 1 := by
      change (-1 : ZMod 2) = 1
      decide
    rw [zero_sub, hnegOne]
    exact isUnit_one
  have hcop :
      IsCoprime (X - C (0 : K)) (X - C (1 : K)) :=
    isCoprime_X_sub_C_of_isUnit_sub hunit
  have hfactor :
      (X - C (0 : K)) * (X - C (1 : K)) =
        (X ^ 2 + X : K[X]) := by
    simp only [map_zero, sub_zero, map_one]
    have htwoPoly : (2 : K[X]) = 0 :=
      CharP.cast_eq_zero (K[X]) 2
    have hsum : (X : K[X]) + X = 0 := by
      calc
        (X : K[X]) + X = 2 * X := by ring
        _ = 0 := by rw [htwoPoly, zero_mul]
    have hnegX : -(X : K[X]) = X := by
      calc
        -(X : K[X]) = -X + (X + X) := by rw [hsum, add_zero]
        _ = X := by ring
    calc
      (X : K[X]) * (X - 1) = X ^ 2 - X := by ring
      _ = X ^ 2 + X := by simp [sub_eq_add_neg, hnegX]
  have hprod_u :
      (X - C (0 : K)) * (X - C (1 : K)) ∣ D.u :=
    hcop.mul_dvd
      (Polynomial.dvd_iff_isRoot.mpr hu0)
      (Polynomial.dvd_iff_isRoot.mpr hu1)
  have hu :
      (X - C (0 : K)) * (X - C (1 : K)) = D.u := by
    have hpdeg :
        ((X - C (0 : K)) * (X - C (1 : K))).natDegree = 2 := by
      rw [natDegree_mul
        (monic_X_sub_C (0 : K)).ne_zero
        (monic_X_sub_C (1 : K)).ne_zero]
      rw [natDegree_X_sub_C, natDegree_X_sub_C]
    apply Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff hprod_u
    · rw [hdeg, hpdeg]
    · rw [((monic_X_sub_C (0 : K)).mul
          (monic_X_sub_C (1 : K))).leadingCoeff,
        D.u_monic.leadingCoeff]
  have hprod_v :
      (X - C (0 : K)) * (X - C (1 : K)) ∣ D.v :=
    hcop.mul_dvd
      (Polynomial.dvd_iff_isRoot.mpr hv0)
      (Polynomial.dvd_iff_isRoot.mpr hv1)
  constructor
  · rw [← hu]
    exact hfactor
  · rw [← hu]
    exact hprod_v
end
end MazurProof.N13SpecialGraphDivisor
end

end

theorem solution : type_of% @MazurProof.N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq := @MazurProof.N13SpecialGraphDivisor.u_eq_base_and_dvd_v_of_graphDivisor_eq
