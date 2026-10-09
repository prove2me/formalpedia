-- Prove2me | solution 1 for MazurProof.N13ProperCurveReduction.reduceCurve_cusp
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:14:30.772984+00:00
-- url     : https://prove2.me/submissions/cd8dc994-4458-4bf0-bbd2-fda5c55b5ecc

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GoodModelTwo_affineEquation_iff_fixed

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

-- ===== FLT.Assumptions.MazurProof.N13ProperCurveReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13ProperCurveReduction =====
section
/-!
# Proper two-chart reduction of N13 curve points at two

Rational points on the sextic are first transported to the generalized
hyperelliptic equation

`y² + (x³ + x + 1)y = x⁵ + x⁴`.

If `x` is integral, its monic equation makes `y` integral and the point
reduces on the affine chart.  If `x` is nonintegral, put `t = x⁻¹` and
`v = t³y`; then the monic infinity-chart equation makes `v` integral,
while positive valuation of `t` forces its residue to be zero.  Thus the
construction is proper and genuinely uses both charts.

The final theorem identifies the reductions of the six rational cusps
with the previously constructed six-point special-fibre equivalence.
No point enumeration is used.
-/
namespace MazurProof.N13ProperCurveReduction
noncomputable section
attribute [local instance] MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT
@[simp] theorem toZMod_mk_one
    (h : ‖(1 : Q₂)‖ ≤ 1) :
    PadicInt.toZMod (⟨1, h⟩ : Z₂) = 1 := by
  have heq : (⟨1, h⟩ : Z₂) = (1 : ℤ_[2]) := by
    apply Subtype.ext
    simp
  rw [heq, map_one]
theorem reduceCurve_cusp
    (c : N13Mumford.Cusp13) :
    reduceCurve (N13Mumford.cuspPoint c) =
      N13SpecialCuspReduction.specialCuspEquiv c := by
  cases c <;>
    simp [reduceCurve, N13Mumford.cuspPoint, reduceAffine,
      reduceIntegralAffine, integralAffineLift,
      ratToQ₂, N13GoodModelTwo.sexticToGoodY,
      N13GoodModelTwo.h,
      N13SpecialCuspReduction.specialCuspEquiv,
      N13SpecialCuspReduction.cuspCoordinateEquiv,
      N13SpecialCuspReduction.cuspCoordinate,
      N13AbelFiberTwoModel.curvePointEquiv] <;>
    norm_num
end
end MazurProof.N13ProperCurveReduction
end

end

theorem solution : type_of% @MazurProof.N13ProperCurveReduction.reduceCurve_cusp := @MazurProof.N13ProperCurveReduction.reduceCurve_cusp
