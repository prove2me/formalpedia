-- Prove2me | solution 1 for MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.derivative_eval_negOne_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:48:17.818907+00:00
-- url     : https://prove2.me/submissions/31e7be8d-9f6b-42bc-9e04-fd0304bf2845

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover =====
section
/-!
# Recovering the N13 two-disk divisor from an integral Mumford graph

Suppose a smooth integral generalized Mumford graph reduces to the fixed
nonspecial graph `(X² + X, 0)`.  Hensel lifting splits its monic quadratic
into one root in each of the residue disks of `0` and `-1`.  Evaluating the
curve relation at those roots and using uniqueness in the vertical Hensel
fibres identifies the graph values with the canonical disk lifts.

Consequently every such integral graph comes from a unique `DiskPair`, up
to the harmless operation of changing its graph polynomial by a multiple
of `u`.  This is the algebraic reverse of
`N13TwoAdicAbelChartData.DiskPair.smoothMumford`; no divisor enumeration or
properness shortcut is used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoAdicAbelChartRecover
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartRecover.instFactPrimeOfNatNat_fLT
namespace NearBaseMumford
variable (D : NearBaseMumford)
theorem derivative_eval_negOne_isUnit :
    IsUnit (D.u.derivative.eval (-1)) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  linear_combination htwo
end NearBaseMumford
end
end MazurProof.N13TwoAdicAbelChartRecover
end

end

theorem solution : type_of% @MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.derivative_eval_negOne_isUnit := @MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.derivative_eval_negOne_isUnit
