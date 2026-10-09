-- Prove2me | solution 1 for MazurProof.N13GaussianNamedUnitSquareclasses.relativeZeta_sq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:33:03.716281+00:00
-- url     : https://prove2.me/submissions/57d1c4b1-7a2a-4aeb-b3b1-8d8c57d079eb

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianGlobalArithmetic =====
section
/-!
# The Gaussian cubic at the ramified prime over 13

This file freezes the global Gaussian arithmetic attached to the actual N13
sextic

`X⁶ + 4X⁵ + 6X⁴ + 2X³ + X² + 2X + 1`.

Over `ℤ[i]` it is the product of a cubic and its conjugate.  The cubic has
discriminant `(3-2i)²`; after translating its root by `9`, it is Eisenstein at
the prime element `3-2i`.  Primality is proved from the Gaussian norm `13`,
and the Eisenstein constant-term test is the single norm nondivisibility
`13 ∤ 62197`.  No class-group computation or factor table is used.
-/
open Polynomial
namespace MazurProof.N13GaussianGlobalArithmetic
noncomputable section
@[simp] theorem i_sq : i ^ 2 = -1 := by
  rfl
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses =====
section
/-!
# Named unit squareclasses in the N13 field

The three displayed N13 units are literal units of the maximal order.  Their
first ramified logarithms are `1`, `α²`, and `α + α²`, hence they are
independent modulo squares.  Dirichlet's theorem gives exactly eight unit
squareclasses, so these three classes form a basis and every maximal-order
unit is their binary product times a square.

The proof uses the genuine global reduction homomorphism from
`N13GaussianGlobalReductionTwo`; no field-unit surrogate or enumeration of
the eight classes is used.
-/
open Function
open Polynomial
namespace MazurProof.N13GaussianNamedUnitSquareclasses
noncomputable section
open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.hKIrreducibleFact
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.fieldL
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraL
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraGI
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraRelativeO
attribute [local instance] MazurProof.N13GaussianNamedUnitSquareclasses.intAlgebraAbsoluteO
/-! ## Literal units of the relative and absolute maximal orders -/
theorem relativeZeta_sq :
    relativeZeta ^ 2 = (-1 : RelativeO) := by
  rw [relativeZeta, relativeI, ← map_pow,
    N13GaussianGlobalArithmetic.i_sq, map_neg, map_one]
/-! ## The global first-jet logarithm -/
/-! ## Structural generation of all unit squareclasses -/
end
end MazurProof.N13GaussianNamedUnitSquareclasses
end

end

theorem solution : type_of% @MazurProof.N13GaussianNamedUnitSquareclasses.relativeZeta_sq := @MazurProof.N13GaussianNamedUnitSquareclasses.relativeZeta_sq
