-- Prove2me | solution 1 for MazurProof.SexticMumford.neg_y_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:51:37.542419+00:00
-- url     : https://prove2.me/submissions/a230e77d-0852-4196-b824-62ec591c4a33

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumford =====
section
/-!
# Balanced Mumford data for a separable monic sextic

This file contains the curve-independent algebra underlying the balanced
Mumford representation for a genus-two curve

`Y² = f(X)`,

where `f` is monic, separable, and has degree six.  Arithmetic for a specific
curve belongs in a separate model instance.

The semantic target is an oriented fractional-ideal quotient of the affine
coordinate ring.  Constructing the order at a chosen point at infinity and
proving the normal-form theorem are deliberately separate later layers.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
namespace Model
end Model
variable (M : Model K)
/-! ## The affine coordinate ring -/
@[simp] theorem yClass_sq :
    yClass M ^ 2 = xClass M M.f := by
  apply AdjoinRoot.mk_eq_mk.mpr
  refine ⟨1, ?_⟩
  simp only [curvePoly]
  ring
/-! ## Balanced triples -/
/-! ## Curve points and their balanced representatives -/
/-! ## Mumford ideals -/
/-! ## The oriented fractional-ideal quotient -/
end
end MazurProof.SexticMumford
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
/-! ## Hyperelliptic conjugation and the quadratic norm -/
theorem neg_y_relation :
    (curvePoly M).eval₂ (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (-(yClass M)) ^ 2 - xClass M M.f = 0
  rw [neg_sq, yClass_sq]
  exact sub_self _
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.neg_y_relation := @MazurProof.SexticMumford.neg_y_relation
