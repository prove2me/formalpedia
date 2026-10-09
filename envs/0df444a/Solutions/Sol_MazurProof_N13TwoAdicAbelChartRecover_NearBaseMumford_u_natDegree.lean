-- Prove2me | solution 1 for MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.u_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:52:19.601711+00:00
-- url     : https://prove2.me/submissions/b8bb2450-d3ce-4346-9954-9a80cc1664de

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
theorem u_natDegree :
    D.u.natDegree = 2 := by
  calc
    D.u.natDegree =
        (D.u.map
          N13GeneralizedMumfordReduction.reduceBase).natDegree :=
      (D.u_monic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase).symm
    _ =
        (N13GeneralizedMumfordReduction.reducePoly D.u).natDegree := rfl
    _ = (X ^ 2 + X : K[X]).natDegree := by rw [D.reduce_u]
    _ = 2 := by
      compute_degree
      norm_num [K, N13GoodCoordinateRingTwo.K,
        N13GoodModelTwo.F2]
end NearBaseMumford
end
end MazurProof.N13TwoAdicAbelChartRecover
end

end

theorem solution : type_of% @MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.u_natDegree := @MazurProof.N13TwoAdicAbelChartRecover.NearBaseMumford.u_natDegree
