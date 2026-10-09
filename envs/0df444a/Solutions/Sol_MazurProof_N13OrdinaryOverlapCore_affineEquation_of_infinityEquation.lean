-- Prove2me | solution 1 for MazurProof.N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:15:16.26909+00:00
-- url     : https://prove2.me/submissions/11196faf-e91f-4f60-b875-1302ed14e630

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13OrdinaryOverlapCore =====
section
/-!
# Coordinate identities on the ordinary N13 overlap

The two algebraic charts are related on their principal opens by

`x = t⁻¹`, `y = t⁻³v`.

This file proves both directions of the coordinate change over an arbitrary
commutative ring.  No cancellation or domain hypothesis is used: the only
input is the explicit inverse relation on the principal open.
-/
namespace MazurProof.N13OrdinaryOverlapCore
/-- The infinity equation implies the affine equation after substituting
`x = t⁻¹` and `y = t⁻³v`. -/
theorem affineEquation_of_infinityEquation
    {S : Type*} [CommRing S]
    (t x v : S)
    (htx : t * x = 1)
    (hInfinity :
      v ^ 2 + (1 + t ^ 2 + t ^ 3) * v = t + t ^ 2) :
    (x ^ 3 * v) ^ 2 +
        (x ^ 3 + x + 1) * (x ^ 3 * v) =
      x ^ 5 + x ^ 4 := by
  have hxt : x * t = 1 := by
    simpa [mul_comm] using htx
  have hx6t : x ^ 6 * t = x ^ 5 := by
    calc
      x ^ 6 * t = x ^ 5 * (x * t) := by ring
      _ = x ^ 5 := by rw [hxt]; ring
  have hx6t2 : x ^ 6 * t ^ 2 = x ^ 4 := by
    calc
      x ^ 6 * t ^ 2 = x ^ 4 * (x * t) ^ 2 := by ring
      _ = x ^ 4 := by rw [hxt]; ring
  have hx6t3 : x ^ 6 * t ^ 3 = x ^ 3 := by
    calc
      x ^ 6 * t ^ 3 = x ^ 3 * (x * t) ^ 3 := by ring
      _ = x ^ 3 := by rw [hxt]; ring
  calc
    (x ^ 3 * v) ^ 2 +
          (x ^ 3 + x + 1) * (x ^ 3 * v) =
        x ^ 6 * v ^ 2 + (x ^ 6 + x ^ 4 + x ^ 3) * v := by
          ring
    _ = x ^ 6 * v ^ 2 +
          (x ^ 6 + x ^ 6 * t ^ 2 + x ^ 6 * t ^ 3) * v := by
          rw [hx6t2, hx6t3]
    _ = x ^ 6 *
          (v ^ 2 + (1 + t ^ 2 + t ^ 3) * v) := by
          ring
    _ = x ^ 6 * (t + t ^ 2) := by rw [hInfinity]
    _ = x ^ 5 + x ^ 4 := by
          rw [mul_add, hx6t, hx6t2]
end MazurProof.N13OrdinaryOverlapCore
end

end

theorem solution : type_of% @MazurProof.N13OrdinaryOverlapCore.affineEquation_of_infinityEquation := @MazurProof.N13OrdinaryOverlapCore.affineEquation_of_infinityEquation
