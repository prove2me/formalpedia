-- Prove2me | solution 1 for MazurProof.RamifiedDlog.fst_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:42:45.212984+00:00
-- url     : https://prove2.me/submissions/fa69eb4a-ca26-4040-bc92-89e130a8f7f6

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.RamifiedDlog =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.RamifiedDlog =====
section
/-!
# The first ramified logarithm

For a field `k`, the units of the dual-number ring
`k[ε] = k ⊕ εk`, `ε² = 0`, have a canonical first-order logarithm

`a + εb ↦ b / a`.

It is additive under multiplication.  In characteristic two it kills
squares, as well as constant units.  This is the structural finite quotient
used by the local N13 fake-descent calculation at two.
-/
namespace MazurProof.RamifiedDlog
open TrivSqZeroExt
noncomputable section
variable {k : Type*} [Field k]
attribute [local instance] MazurProof.RamifiedDlog.dualNumberUnitsIsMulCommutative
/-- The residue of a dual-number unit is nonzero. -/
theorem fst_ne_zero (z : (DualNumber k)ˣ) :
    fst (z : DualNumber k) ≠ 0 := by
  have hz :
      IsUnit (fst (z : DualNumber k)) :=
    z.isUnit.map (fstHom k k k).toRingHom
  exact hz.ne_zero
end
end MazurProof.RamifiedDlog
end

end

theorem solution : type_of% @MazurProof.RamifiedDlog.fst_ne_zero := @MazurProof.RamifiedDlog.fst_ne_zero
