-- Prove2me | solution 1 for MazurProof.N13SexticSquareclass.compressed_scaled_identity_in_algebra
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:17:49.857986+00:00
-- url     : https://prove2.me/submissions/a5a37b43-e28b-4785-8f84-b4e4a0bbd1b6

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
/-- The compressed squareclass identity: in `ℚ[T]/(f)`,
`(-C) * (B / 2)^2 = 13`. -/
theorem compressed_squareclass_identity : C * B ^ 2 + 52 = f * r13 := by
  simp [f, N13Mumford.f, B, C, r13]
  ring
theorem compressed_scaled_reduction :
    (-C) * (Polynomial.C (1 / 2 : ℚ) * B) ^ 2 -
        Polynomial.C (13 : ℚ) =
      f * (Polynomial.C (-1 / 4 : ℚ) * r13) := by
  calc
    _ = Polynomial.C (-1 / 4 : ℚ) * (C * B ^ 2 + 52) := by
      have hnegQuarter :
          -((Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 2) =
            Polynomial.C (-1 / 4 : ℚ) := by
        rw [← map_pow, ← map_neg]
        norm_num
      have hthirteen :
          (Polynomial.C (-1 / 4 : ℚ) : ℚ[X]) * 52 =
            -(Polynomial.C (13 : ℚ)) := by
        rw [show (52 : ℚ[X]) = Polynomial.C (52 : ℚ) by
              exact (map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 52).symm,
          ← map_mul, ← map_neg]
        norm_num
      calc
        _ = -((Polynomial.C (1 / 2 : ℚ) : ℚ[X]) ^ 2) *
              (C * B ^ 2) - Polynomial.C (13 : ℚ) := by ring
        _ = Polynomial.C (-1 / 4 : ℚ) * (C * B ^ 2) +
              Polynomial.C (-1 / 4 : ℚ) * 52 := by
                rw [hnegQuarter, hthirteen]
                ring
        _ = _ := by ring
    _ = Polynomial.C (-1 / 4 : ℚ) * (f * r13) := by
      rw [compressed_squareclass_identity]
    _ = _ := by ring
theorem ofPoly_eq_of_sub_eq_mul
    (p q r : ℚ[X]) (h : p - q = f * r) :
    ofPoly p = ofPoly q := by
  have hm := congrArg (AdjoinRoot.mk f) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul] at hm
  exact sub_eq_zero.mp hm
theorem compressed_scaled_identity_in_algebra :
    (-(ofPoly C)) * (halfOfPoly B) ^ 2 =
      algebraMap ℚ SexticAlgebra 13 := by
  have hm := ofPoly_eq_of_sub_eq_mul
    ((-C) * (Polynomial.C (1 / 2 : ℚ) * B) ^ 2)
    (Polynomial.C (13 : ℚ))
    (Polynomial.C (-1 / 4 : ℚ) * r13)
    compressed_scaled_reduction
  simpa [halfOfPoly, ofPoly, map_mul, map_pow] using hm
end
end MazurProof.N13SexticSquareclass
end

end

theorem solution : type_of% @MazurProof.N13SexticSquareclass.compressed_scaled_identity_in_algebra := @MazurProof.N13SexticSquareclass.compressed_scaled_identity_in_algebra
