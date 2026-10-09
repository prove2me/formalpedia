-- Prove2me | solution 1 for MazurProof.N13GaussianGlobalArithmetic.g_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:39:37.175271+00:00
-- url     : https://prove2.me/submissions/0007857b-1eea-4638-a7ae-e30948f13525

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
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
/-- The displayed cubic and its conjugate recover the exact N13 sextic. -/
theorem g_mul_conj :
    g * gConj = n13F := by
  have hCi : (C i : GI[X]) ^ 2 = -1 := by
    rw [← map_pow, i_sq, map_neg, map_one]
  simp only [g, gConj, n13F, map_add, map_sub, map_mul,
    map_ofNat, map_neg, map_one]
  ring_nf
  rw [hCi]
  ring
end
end MazurProof.N13GaussianGlobalArithmetic
end

end

theorem solution : type_of% @MazurProof.N13GaussianGlobalArithmetic.g_mul_conj := @MazurProof.N13GaussianGlobalArithmetic.g_mul_conj
