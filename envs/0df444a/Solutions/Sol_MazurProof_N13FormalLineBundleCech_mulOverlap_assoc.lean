-- Prove2me | solution 1 for MazurProof.N13FormalLineBundleCech.mulOverlap_assoc
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:41:11.162139+00:00
-- url     : https://prove2.me/submissions/ec563a86-9b21-4aee-bfbd-59521e6835be

import Mathlib
import Definitions.Def_MazurN13_L4

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13FormalLineBundleCech =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalLineBundleCech =====
section
/-!
# Near-trivial formal line bundles in the N13 Čech chart

A line bundle in the kernel of specialization admits, after choosing local
trivializations, a formal overlap transition which reduces to `1`.  Twisting
the two actual principal parts by such a transition perturbs the integral
connecting matrix, but does not change its special fibre.

This file encodes the actual quadratic formal curve algebra at infinity,
proves coefficientwise reduction respects its multiplication, and applies
the previously proved Čech--Nakayama theorem to every invertible transition
reducing to `1`.

The remaining geometric task is now sharply isolated: construct these two
local trivializations from a rational Picard class in the specialization
kernel.  No cohomology or matrix-surjectivity hypothesis remains.
-/
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalLineBundleCech.instFactPrimeOfNatNat_fLT
theorem mulOverlap_assoc
    {R : Type*} [CommRing R]
    (x y z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap (mulOverlap x y) z =
      mulOverlap x (mulOverlap y z) := by
  apply Prod.ext <;>
    simp [mulOverlap]
  <;> ring
namespace NearIdentityTransition
variable (g : NearIdentityTransition)
end NearIdentityTransition
end
end MazurProof.N13FormalLineBundleCech
end

end

theorem solution : type_of% @MazurProof.N13FormalLineBundleCech.mulOverlap_assoc := @MazurProof.N13FormalLineBundleCech.mulOverlap_assoc
