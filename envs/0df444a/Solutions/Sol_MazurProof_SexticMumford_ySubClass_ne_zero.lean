-- Prove2me | solution 1 for MazurProof.SexticMumford.ySubClass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:52:21.442755+00:00
-- url     : https://prove2.me/submissions/d6b8f517-8677-4673-a14b-72c99bf1fc80

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordNorm =====
section
/-!
# Structural identities for the quadratic norm

The hyperelliptic norm is multiplicative, fixes the polynomial subring, and
can be read off from the two canonical coefficients.  These facts are kept
separate from any curve-specific degree calculation.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
@[simp] theorem coeffY_ySubClass (M : Model K) (v : K[X]) :
    coeffY M (ySubClass M v) = 1 := by
  simp [ySubClass]
end
end MazurProof.SexticMumford
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordCantorReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordCantorReduction =====
section
/-!
# One-step Cantor reduction for a monic sextic

This file isolates the structural algebra used by a well-founded Cantor
reduction.  It contains no enumeration and no Riemann--Roch input.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
attribute [local instance] MazurProof.SexticMumford.instDecidableEq_fLT
/-! ## Changing the graph polynomial modulo `u` -/
/-! ## The Cantor product identity -/
/-! ## Degree descent -/
/-! ## The normalized next semirepresentative -/
/-! ## Conjugating the complement -/
/-! ## Principal functions in one oriented step -/
theorem ySubClass_ne_zero (V : K[X]) :
    ySubClass M V ≠ 0 := by
  intro h
  have hcoeff : (1 : K[X]) = 0 := by
    simpa using congrArg (coeffY M) h
  exact one_ne_zero hcoeff
/-! ## Exact oriented update -/
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.ySubClass_ne_zero := @MazurProof.SexticMumford.ySubClass_ne_zero
