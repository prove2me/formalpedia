-- Prove2me | solution 1 for MazurProof.N13GoodPointFirstJet.root_jet
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:56:04.536035+00:00
-- url     : https://prove2.me/submissions/1a105423-3a0b-4ecb-ad1b-2dc0e358cad3

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

-- ===== FLT.Assumptions.MazurProof.N13GoodPointFirstJet =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodPointFirstJet =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

An actual point and implicit tangent on the good quadratic curve define a
ring map to dual numbers. Squared graph-ideal membership therefore forces
both the value and first derivative of a regular function to vanish.
Only this direction is needed for the principal/Hermite matching step.
-/
namespace MazurProof.N13GoodPointFirstJet
noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]
theorem polynomialJet_apply (x : K) (p : K[X]) :
    polynomialJet x p = (p.eval x, p.derivative.eval x) := rfl
theorem root_jet
    (x y s : K)
    (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
    (hd : (2 * y + (x ^ 3 + x + 1)) * s +
      (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0) :
    (N13GeneralizedMumfordIntegral.curvePoly (R := K)).eval₂
      (polynomialJet x) (y, s) = 0 := by
  apply TrivSqZeroExt.ext
  · simp only [N13GeneralizedMumfordIntegral.curvePoly,
      N13GeneralizedMumfordIntegral.hPoly, N13GeneralizedMumfordIntegral.rhsPoly,
      eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one,
      polynomialJet_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_zero,
      eval_X, eval_add, eval_pow, eval_one, eval_C, TrivSqZeroExt.fst_mk]
    linear_combination hc
  · simp only [N13GeneralizedMumfordIntegral.curvePoly,
      N13GeneralizedMumfordIntegral.hPoly, N13GeneralizedMumfordIntegral.rhsPoly,
      eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one,
      polynomialJet_apply]
    simp [derivative_mul, derivative_pow, smul_eq_mul, op_smul_eq_smul, nsmul_eq_mul,
      TrivSqZeroExt.snd_pow]
    linear_combination hd
section
variable (x y s : K)
variable (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
variable (hd : (2 * y + (x ^ 3 + x + 1)) * s + (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0)
end
end
end MazurProof.N13GoodPointFirstJet
end

end

theorem solution : type_of% @MazurProof.N13GoodPointFirstJet.root_jet := @MazurProof.N13GoodPointFirstJet.root_jet
