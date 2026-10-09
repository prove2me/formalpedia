-- Prove2me | solution 1 for MazurProof.N13AbelChartBase.specialBaseDivisor_not_canonical
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:56:27.846972+00:00
-- url     : https://prove2.me/submissions/351cc871-b047-46cb-af14-ae608809c9af

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13AbelChartBase =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13AbelChartBase =====
section
/-!
# The nonspecial base divisor for the N13 Abel chart

The integral divisor

`(0,0) + (-1,0)`

has generalized Mumford pair `u = X² + X`, `v = 0`.  Its reduction is the
unordered pair of the sheet-zero points over the distinct affine base
coordinates `0` and `1`.  A canonical hyperelliptic fibre contains one
point on each sheet, so this reduced divisor is noncanonical.

The same base pair satisfies a short Bézout identity.  Hence its graph ideal
is one of the smooth integral Mumford ideals already shown to commute with
reduction.
-/
open Polynomial
namespace MazurProof.N13AbelChartBase
noncomputable section
open N13AbelFiberTwoModel
open N13SymmetricSquareTwo
attribute [local instance] MazurProof.N13AbelChartBase.instFactPrimeOfNatNat_fLT
@[simp] theorem sheet_p00 :
    sheet p00 = 0 := by
  simp [sheet, p00]
@[simp] theorem sheet_p10 :
    sheet p10 = 0 := by
  simp [sheet, p10]
@[simp] theorem sheet_canonical_one
    (b : BasePoint) :
    sheet (curvePointEquiv.symm (b, 1)) = 1 := by
  simp [sheet]
/-- The base divisor is outside the canonical hyperelliptic pencil.  The
proof only compares sheet coordinates; it does not enumerate curve points. -/
theorem specialBaseDivisor_not_canonical :
    ¬IsCanonical specialBaseDivisor := by
  rintro ⟨b, hb⟩
  change
    s(curvePointEquiv.symm (b, 0),
      curvePointEquiv.symm (b, 1)) =
        s(p00, p10) at hb
  rw [Sym2.eq_iff] at hb
  rcases hb with hb | hb
  · have hs := congrArg sheet hb.2
    simp at hs
  · have hs := congrArg sheet hb.2
    simp at hs
end
end MazurProof.N13AbelChartBase
end

end

theorem solution : type_of% @MazurProof.N13AbelChartBase.specialBaseDivisor_not_canonical := @MazurProof.N13AbelChartBase.specialBaseDivisor_not_canonical
