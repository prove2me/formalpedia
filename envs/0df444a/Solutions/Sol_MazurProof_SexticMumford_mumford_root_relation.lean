-- Prove2me | solution 1 for MazurProof.SexticMumford.mumford_root_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:51:31.934186+00:00
-- url     : https://prove2.me/submissions/0f7acac9-792d-4579-98b4-8e50363a367d

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordIdeal =====
section
/-!
# Mumford evaluation ideals for a smooth sextic affine ring

For a model `Y² = f(X)`, quotient evaluation `X ↦ X mod u`, `Y ↦ v mod u`
has kernel exactly `(u, Y - v)`.  This recovers canonical Mumford
polynomials from their ideal and is the algebraic core of normal-form
uniqueness.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem mumford_root_relation (D : SemiMumford M) :
    (curvePoly M).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 - M.f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨w, hw⟩ := D.curve_dvd
  refine ⟨-w, ?_⟩
  calc
    D.v ^ 2 - M.f = -(M.f - D.v ^ 2) := by ring
    _ = -(D.u * w) := by rw [hw]
    _ = D.u * (-w) := by ring
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.mumford_root_relation := @MazurProof.SexticMumford.mumford_root_relation
