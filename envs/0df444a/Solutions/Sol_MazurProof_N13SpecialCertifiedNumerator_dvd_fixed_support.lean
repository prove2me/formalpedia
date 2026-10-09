-- Prove2me | solution 1 for MazurProof.N13SpecialCertifiedNumerator.dvd_fixed_support
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:21:04.973189+00:00
-- url     : https://prove2.me/submissions/6e6b37bc-e18e-47dd-8668-5477ad054e55

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialCertifiedNumerator =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialCertifiedNumerator =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Encode the actual small numerator supplied by a SpecialComparison in the
finite coefficient arrays, and feed its proved norm-support condition into
the finite kernel certificate. No bounded-function enumeration is assumed.
-/
namespace MazurProof.N13SpecialCertifiedNumerator
noncomputable section
open Polynomial N13SpecialSmallFunctionCertificate
open N13SpecialDivisorCharts
open N13SpecialComparisonFactorPair
theorem dvd_fixed_support (p : K[X]) (i j : ℕ) (hij : i + j ≤ 16)
    (hp : p ∣ X ^ i * (X - 1) ^ j) : p ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply dvd_trans hp
  refine ⟨X ^ (16 - i) * (X - 1) ^ (16 - j), ?_⟩
  have hi : i + (16 - i) = 16 := by omega
  have hj : j + (16 - j) = 16 := by omega
  calc
    (X : K[X]) ^ 16 * (X - 1) ^ 16 =
        (X ^ i * X ^ (16 - i)) * ((X - 1) ^ j * (X - 1) ^ (16 - j)) := by
          rw [← pow_add, ← pow_add, hi, hj]
    _ = _ := by ring
end
end MazurProof.N13SpecialCertifiedNumerator
end

end

theorem solution : type_of% @MazurProof.N13SpecialCertifiedNumerator.dvd_fixed_support := @MazurProof.N13SpecialCertifiedNumerator.dvd_fixed_support
