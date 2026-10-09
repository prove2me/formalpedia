-- Prove2me | solution 1 for MazurProof.N13SpecialLaurentBranches.root_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:38:21.837986+00:00
-- url     : https://prove2.me/submissions/fb21aba1-f9c2-43db-9e3e-cab3cf3dbddf

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialLaurentBranches =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialLaurentBranches =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Actual Laurent expansions of the GOOD characteristic-two affine model.
The branch difference is h(x), not twice a square root. The resulting
two-infinity pole bound forces deg(A)<=d and deg(B)+3<=d for A+B*y.
-/
namespace MazurProof.N13SpecialLaurentBranches
noncomputable section
open Polynomial
open scoped LaurentSeries
theorem base_X : base X = t⁻¹ := by
  simp only [base, N13BranchNorm.evalPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl
theorem root_relation (r : P)
    (hr : r ^ 2 + N13SpecialInfinityBranchJets.h * r - N13SpecialInfinityBranchJets.rhs = 0) :
    N13GoodCoordinateRingTwo.curvePoly.eval₂ base (t⁻¹ ^ 3 * includeSeries r) = 0 := by
  have hl := congrArg includeSeries hr
  simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hl
  have hh : includeSeries N13SpecialInfinityBranchJets.h = 1 + t ^ 2 + t ^ 3 := by
    simp [N13SpecialInfinityBranchJets.h, includeSeries, N13LaurentPolynomialOrder.parameter]
  have hrhs : includeSeries N13SpecialInfinityBranchJets.rhs = t + t ^ 2 := by
    simp [N13SpecialInfinityBranchJets.rhs, includeSeries, N13LaurentPolynomialOrder.parameter]
  rw [hh, hrhs] at hl
  have he : (t⁻¹ ^ 3 * includeSeries r) ^ 2 +
      (t⁻¹ ^ 3 + t⁻¹ + 1) * (t⁻¹ ^ 3 * includeSeries r) - (t⁻¹ ^ 5 + t⁻¹ ^ 4) = 0 := by
    apply mul_left_cancel₀ (pow_ne_zero 6 t_ne_zero)
    calc
      t ^ 6 * ((t⁻¹ ^ 3 * includeSeries r) ^ 2 +
          (t⁻¹ ^ 3 + t⁻¹ + 1) * (t⁻¹ ^ 3 * includeSeries r) - (t⁻¹ ^ 5 + t⁻¹ ^ 4)) =
        (includeSeries r) ^ 2 + (1 + t ^ 2 + t ^ 3) * includeSeries r - (t + t ^ 2) := by
          field_simp [t_ne_zero]
          try ring
      _ = t ^ 6 * 0 := by rw [hl, mul_zero]
  simp only [N13GoodCoordinateRingTwo.curvePoly, N13GoodCoordinateRingTwo.hPoly,
    N13GoodCoordinateRingTwo.rhsPoly, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X,
    eval₂_C, eval₂_one, map_add, map_pow, map_one, base_X]
  linear_combination he
end
end MazurProof.N13SpecialLaurentBranches
end

end

theorem solution : type_of% @MazurProof.N13SpecialLaurentBranches.root_relation := @MazurProof.N13SpecialLaurentBranches.root_relation
