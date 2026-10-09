-- Prove2me | solution 1 for MazurProof.N13SexticSquareclass.zeta_mul_e1_mul_primeA
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:19:16.737113+00:00
-- url     : https://prove2.me/submissions/a210e003-5baf-4a8b-98dc-4c5d89348fec

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
theorem zeta_e1_a_reduction : Z * E₁ * A - 4 * B = f * rB := by
  simp [f, N13Mumford.f, Z, E₁, A, B, rB]
  ring
theorem zeta_e1_a_scaled_reduction :
    (Polynomial.C (1 / 2 : ℚ) * Z) *
          (Polynomial.C (1 / 2 : ℚ) * E₁) *
          (Polynomial.C (1 / 2 : ℚ) * A) -
        Polynomial.C (1 / 2 : ℚ) * B =
      f * (Polynomial.C (1 / 8 : ℚ) * rB) := by
  calc
    _ = Polynomial.C (1 / 8 : ℚ) * (Z * E₁ * A - 4 * B) := by
      have hcube :
          (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 =
            Polynomial.C (1 / 8 : ℚ) := by
        rw [← map_pow]
        norm_num
      have hfour :
          (Polynomial.C (1 / 8 : ℚ) : ℚ[X]) * 4 =
            Polynomial.C (1 / 2 : ℚ) := by
        rw [show (4 : ℚ[X]) = Polynomial.C (4 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 4).symm,
          ← map_mul]
        norm_num
      calc
        _ = (Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 3 *
              (Z * E₁ * A) -
            Polynomial.C (1 / 2 : ℚ) * B := by ring
        _ = Polynomial.C (1 / 8 : ℚ) * (Z * E₁ * A) -
            (Polynomial.C (1 / 8 : ℚ) * 4) * B := by
              rw [hcube, hfour]
        _ = _ := by ring
    _ = Polynomial.C (1 / 8 : ℚ) * (f * rB) := by
      rw [zeta_e1_a_reduction]
    _ = _ := by ring
theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm
theorem zeta_mul_e1_mul_primeA :
    zeta * e1 * primeA = halfOfPoly B := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((Polynomial.C (1 / 2 : ℚ) * Z) *
      (Polynomial.C (1 / 2 : ℚ) * E₁) *
      (Polynomial.C (1 / 2 : ℚ) * A))
    (Polynomial.C (1 / 2 : ℚ) * B)
    (Polynomial.C (1 / 8 : ℚ) * rB)
    zeta_e1_a_scaled_reduction
  simpa [zeta, e1, primeA, halfOfPoly, ofPoly, map_mul] using hm
end
end MazurProof.N13SexticSquareclass
end

end

theorem solution : type_of% @MazurProof.N13SexticSquareclass.zeta_mul_e1_mul_primeA := @MazurProof.N13SexticSquareclass.zeta_mul_e1_mul_primeA
