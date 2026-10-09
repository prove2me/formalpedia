-- Prove2me | solution 1 for MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:50:25.948012+00:00
-- url     : https://prove2.me/submissions/a52507fd-e89c-4038-b147-839978f0d25c

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralAffinePointSpread =====
section
/-!
# Integral spreads of affine N13 points

An integral point of the good two-adic affine chart gives the monic linear
generalized Mumford graph `(X-x, y)`.  Its curve equation follows by the
factor theorem.  Completion of the square identifies its generic sextic
graph with the standard Mumford graph of the corresponding curve point.

The semigraph contraction theorem and the global Jacobian frame therefore
make the canonical divisorial spread invertible.  This closes the affine
half of the proper degree-one branch without local factoriality.
-/
open Polynomial
namespace MazurProof.N13IntegralAffinePointSpread
noncomputable section
attribute [local instance] MazurProof.N13IntegralAffinePointSpread.instFactPrimeOfNatNat_fLT
@[simp] theorem sexticSemi_v (P : IntegralPoint) :
    (N13TwoAdicMumfordTransport.sexticSemiOfSemi
      (integralSemiGraph P) 0).v =
      C (sexticY P) := by
  rw [N13TwoAdicMumfordTransport.sexticSemiOfSemi_v]
  simp [integralSemiGraph, pointU, pointV,
    N13TwoAdicMumfordTransport.mapPoly,
    N13TwoAdicMumfordTransport.coeffMap,
    N13GoodSexticMumfordTransport.reducedCompletedGraph,
    N13GoodSexticMumfordTransport.completedGraph,
    mod_X_sub_C_eq_C_eval, sexticY,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GoodModelTwo.h]
/-! ## The integral branch of the selected degree-one Padé graph -/
end
end MazurProof.N13IntegralAffinePointSpread
end

end

theorem solution : type_of% @MazurProof.N13IntegralAffinePointSpread.sexticSemi_v := @MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
