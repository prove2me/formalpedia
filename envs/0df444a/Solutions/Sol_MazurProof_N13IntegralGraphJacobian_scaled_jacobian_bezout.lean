-- Prove2me | solution 1 for MazurProof.N13IntegralGraphJacobian.scaled_jacobian_bezout
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:44:05.164534+00:00
-- url     : https://prove2.me/submissions/1a91225d-ec1a-4842-8598-3dcf51f8a7b1

import Mathlib
import Definitions.Def_MazurN13_L1
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_yClass_relation
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_yClass_relation

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
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
@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n
@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
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
@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : K[X]) = (n : CoordinateRing) :=
  map_natCast xClassHom n
@[simp] theorem xClass_add (p q : K[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q
/-! ## Hyperelliptic conjugation and the quadratic norm -/
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralGraphJacobian =====
section
/-!
# Integral N13 graph ideals and the affine Jacobian

This file instantiates the generic graph-Jacobian dual frame for the good
integral N13 equation.  A short resultant certificate proves that the two
relative Jacobian rows generate one globally, so every integral Mumford
graph ideal is invertible.  No fixed special graph or point classification
is used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralGraphJacobian
noncomputable section
attribute [local instance] MazurProof.N13IntegralGraphJacobian.instFactPrimeOfNatNat_fLT
open N13GeneralizedMumfordIntegral
theorem derivative_hPoly_explicit :
    derivative (hPoly (R := R₂)) =
      (3 : R₂[X]) * X ^ 2 + 1 := by
  simp [hPoly, derivative_add, derivative_pow]
  exact map_natCast C 3
theorem derivative_rhsPoly_explicit :
    derivative (rhsPoly (R := R₂)) =
      (5 : R₂[X]) * X ^ 4 +
        (4 : R₂[X]) * X ^ 3 := by
  simp [rhsPoly, derivative_add, derivative_pow]
  congr 1
/-- The integral resultant certificate for the two relative Jacobian
rows.  It comes from the univariate Euclidean identity between
`h² + 4 * rhs` and `h' * h + 2 * rhs'`; its right-hand side is the
optimal odd scalar `13`. -/
theorem scaled_jacobian_bezout :
    bezoutA * jacobianX + bezoutB * jacobianY =
      (13 : IntegralRing) := by
  have hcurve :=
    yClass_relation (R := R₂)
  simp only [jacobianX, derivative_hPoly_explicit,
    derivative_rhsPoly_explicit, xClass_add,
    xClass_mul, xClass_pow]
  have h3 :
      xClass (R := R₂) (3 : R₂[X]) =
        (3 : IntegralRing) :=
    xClass_natCast 3
  have h4 :
      xClass (R := R₂) (4 : R₂[X]) =
        (4 : IntegralRing) :=
    xClass_natCast 4
  have h5 :
      xClass (R := R₂) (5 : R₂[X]) =
        (5 : IntegralRing) :=
    xClass_natCast 5
  rw [h3, h4, h5]
  simp [bezoutA, bezoutB, jacobianY,
    hPoly, rhsPoly] at hcurve ⊢
  linear_combination
    (150 * xClass (R := R₂) X ^ 4 +
      392 * xClass (R := R₂) X ^ 3 +
      303 * xClass (R := R₂) X ^ 2 -
      96 * xClass (R := R₂) X + 117) * hcurve
/-! ## Graphs without a monicity hypothesis

Monicity is needed by the quotient-basis and contraction arguments, but not
by the Jacobian dual frame.  The following version isolates the exact
regularity input here: the horizontal graph equation is merely nonzero.
-/
end
end MazurProof.N13IntegralGraphJacobian
end

end

theorem solution : type_of% @MazurProof.N13IntegralGraphJacobian.scaled_jacobian_bezout := @MazurProof.N13IntegralGraphJacobian.scaled_jacobian_bezout
