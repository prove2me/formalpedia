-- Prove2me | solution 1 for MazurProof.N13SexticSquareclass.e2_mul_primeA_mul_primeQ
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:21:27.413615+00:00
-- url     : https://prove2.me/submissions/9ffbc4c2-127d-457b-b733-c25da837301b

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SexticSquareclass =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SexticSquareclass =====
section
/-!
# The rational-scalar survivor in the N13 fake square-class target

The apparent second local survivor in the weak two-descent is not a second
geometric class.  In the sextic algebra it differs from `13` by an explicit
square.  The proof first compresses the five power-basis expressions to two
degree-five polynomials `B` and `C`; it never expands the final product to
degree thirty-three.
-/
open Polynomial
namespace MazurProof.N13SexticSquareclass
noncomputable section
theorem e2_a_q_reduction : E₂ * A * Q + 8 * C = f * rC := by
  simp [f, N13Mumford.f, E₂, A, Q, C, rC]
  ring
theorem e2_a_q_scaled_reduction :
    (Polynomial.C (1 / 2 : ℚ) * E₂) *
          (Polynomial.C (1 / 2 : ℚ) * A) *
          (Polynomial.C (1 / 2 : ℚ) * Q) -
        (-C) =
      f * (Polynomial.C (1 / 8 : ℚ) * rC) := by
  calc
    _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q + 8 * C) := by
      have hcube :
          (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 =
            Polynomial.C (1 / 8 : ℚ) := by
        rw [← map_pow]
        norm_num
      have height :
          (Polynomial.C (1 / 8 : ℚ) : ℚ[X]) * 8 = 1 := by
        rw [show (8 : ℚ[X]) = Polynomial.C (8 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 8).symm,
          ← map_mul]
        norm_num
      calc
        _ = (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 *
              (E₂ * A * Q) + C := by ring
        _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q) + 1 * C := by
              rw [hcube]
              simp
        _ = Polynomial.C (1 / 8 : ℚ) * (E₂ * A * Q) +
              (Polynomial.C (1 / 8 : ℚ) * 8) * C := by
                rw [height]
        _ = _ := by ring
    _ = Polynomial.C (1 / 8 : ℚ) * (f * rC) := by
      rw [e2_a_q_reduction]
    _ = _ := by ring
theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm
theorem e2_mul_primeA_mul_primeQ :
    e2 * primeA * primeQ = -(ofPoly C) := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((Polynomial.C (1 / 2 : ℚ) * E₂) *
      (Polynomial.C (1 / 2 : ℚ) * A) *
      (Polynomial.C (1 / 2 : ℚ) * Q))
    (-C)
    (Polynomial.C (1 / 8 : ℚ) * rC)
    e2_a_q_scaled_reduction
  simpa [e2, primeA, primeQ, halfOfPoly, ofPoly, map_mul] using hm
end
end MazurProof.N13SexticSquareclass
end

end

theorem solution : type_of% @MazurProof.N13SexticSquareclass.e2_mul_primeA_mul_primeQ := @MazurProof.N13SexticSquareclass.e2_mul_primeA_mul_primeQ
