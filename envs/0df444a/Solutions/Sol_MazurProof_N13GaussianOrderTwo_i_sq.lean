-- Prove2me | solution 1 for MazurProof.N13GaussianOrderTwo.i_sq
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:58:17.840713+00:00
-- url     : https://prove2.me/submissions/493c3cb9-636e-47a3-b1c3-c5022e199a69

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GaussianFieldEquiv_gaussianI_sq

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
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

-- ===== FLT.Assumptions.MazurProof.N13GaussianOrderTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianOrderTwo =====
section
/-!
# The fixed Gaussian order at two for N13

This file constructs the first ramified quotient directly from the
Gaussian cubic presentation.  We first adjoin a root `i` of `T² + 1`
over `ℤ₂`, and then a root `θ` of

`T³ + 2T² - T - 1 - i(2T(T+1))`.

Sending `i` to `1 + ε` and `θ` to the cubic residue `α` defines a
surjective ring homomorphism to `𝔽₈[ε]/(ε²)`.  Its kernel is proved to
be exactly `(1-i)² = (2)` by the two nested monic power bases.  Hence the
ramified-prime-square quotient is identified with the dual-number ring.
This is the direct quotient-ring core needed by the local N13 descent;
no ray-class enumeration is involved.

The remaining arithmetic identification with the completed maximal
order is recorded separately in `scratch/N13_GAUSSIAN_ORDER_TWO.md`.
-/
open Polynomial
open scoped CharTwo
namespace MazurProof.N13GaussianOrderTwo
noncomputable section
open N13LocalDlogTwo
open N13LocalDlogRegimes
open TrivSqZeroExt
open Module
/-! ## The integral Gaussian cubic order -/
theorem gaussianI_sq :
    gaussianI ^ 2 = -1 := by
  have h : gaussianI ^ 2 + 1 = 0 := by
    have hs :
        AdjoinRoot.mk gaussianPolynomial gaussianPolynomial = 0 :=
      AdjoinRoot.mk_self
    change (AdjoinRoot.mk gaussianPolynomial X) ^ 2 + 1 = 0 at hs
    exact hs
  exact eq_neg_of_add_eq_zero_left h
theorem i_sq :
    i ^ 2 = -1 := by
  rw [i, ← map_pow, gaussianI_sq, map_neg, map_one]
/-! ## The two nested power bases -/
/-! ## Direct reduction to the dual-number ring -/
/-! ## Exactness of the first-jet quotient -/
/-! ## Compatibility with the N13 descent generators -/
/-! ## The ramified prime square -/
/-! ## Structural surjectivity -/
end
end MazurProof.N13GaussianOrderTwo
end

end

theorem solution : type_of% @MazurProof.N13GaussianOrderTwo.i_sq := @MazurProof.N13GaussianOrderTwo.i_sq
