-- Prove2me | solution 1 for MazurProof.N13GoodCoordinateRingTwo.recompose
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:48:11.702065+00:00
-- url     : https://prove2.me/submissions/2b5788e6-530c-4d39-9d70-5d7b7a9482ac

import Mathlib
import Definitions.Def_MazurN13_L1
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
theorem normalPoly_eq_C_add_C_mul_X
    [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
theorem curvePoly_degree : curvePoly.degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num
theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
/-- Every coordinate-ring element has a unique rank-two expression. -/
theorem recompose (z : CoordinateRing) :
    xClass (coeff0 z) + xClass (coeffY z) * yClass = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass (coeff0 (mk g)) +
              xClass (coeffY (mk g)) * yClass =
            mk
              (C (coeff0 (mk g)) +
                C (coeffY (mk g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = mk (normalPoly (mk g)) := by
              rw [normalPoly_eq_C_add_C_mul_X]
        _ = mk g :=
          AdjoinRoot.mk_leftInverse curvePoly_monic (mk g)
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

theorem solution : type_of% @MazurProof.N13GoodCoordinateRingTwo.recompose := @MazurProof.N13GoodCoordinateRingTwo.recompose
