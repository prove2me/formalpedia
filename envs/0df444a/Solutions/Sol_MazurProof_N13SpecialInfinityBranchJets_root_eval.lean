-- Prove2me | solution 1 for MazurProof.N13SpecialInfinityBranchJets.root_eval
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:35:28.434997+00:00
-- url     : https://prove2.me/submissions/b4954ccd-a331-47b1-9c6e-b86732c195e2

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialInfinityBranchJets =====
section
/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

The actual characteristic-two infinity chart has two power-series branches
obtained by reducing the integral Hensel roots. Both n-jets vanish exactly
on the principal ideal (t^n). This is special-fibre geometry, independent of
the unreviewed calibrated chooser and of the missing special-code theorem.
-/
namespace MazurProof.N13SpecialInfinityBranchJets
noncomputable section
open Polynomial
attribute [local instance] MazurProof.N13SpecialInfinityBranchJets.instFactPrimeOfNatNat_fLT
theorem root_eval (r : P) (hr : r ^ 2 + h * r - rhs = 0) :
    N13SpecialInfinityChart.curvePoly.eval₂ beta r = 0 := by
  simpa [N13SpecialInfinityChart.curvePoly, N13SpecialInfinityChart.hPoly,
    N13SpecialInfinityChart.rhsPoly, beta, h, rhs, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hr
end
end MazurProof.N13SpecialInfinityBranchJets
end

end

theorem solution : type_of% @MazurProof.N13SpecialInfinityBranchJets.root_eval := @MazurProof.N13SpecialInfinityBranchJets.root_eval
