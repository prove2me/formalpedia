-- Prove2me | solution 1 for MazurProof.N13IntegralModelContraction.goodRing_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:58:21.376994+00:00
-- url     : https://prove2.me/submissions/853c8bf2-a734-43c1-97e3-46ac91024d7e

import Mathlib
import Definitions.Def_MazurN13_L2
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralModelContraction =====
section
/-!
# Vertical localization and ideal contraction for the N13 integral model

The affine coordinate ring of the N13 generic fibre is obtained from the
integral good-model coordinate ring by inverting only the nonzero scalars of
`ℤ₂`.  The proof uses the rank-two normal form `p(x) + q(x)y`: a common
scalar denominator clears the two coefficient polynomials simultaneously.

Consequently every ideal on the generic affine fibre has a canonical
contraction to the integral model, and extending this contraction recovers
the original ideal exactly.  The contraction is vertically saturated.  This
is the algebraic integral-model layer needed before taking a reflexive hull
or lifting a section; it does not assert that the contracted ideal is already
invertible on the two-dimensional integral surface.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralModelContraction
noncomputable section
attribute [local instance] MazurProof.N13IntegralModelContraction.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralModelContraction.integralGoodAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialAlgebra
attribute [local instance] MazurProof.N13IntegralModelContraction.polynomialLocalization
@[simp] theorem integralToGood_algebraMap
    (a : R₂) :
    integralToGood (algebraMap R₂ IntegralRing a) =
      algebraMap Q₂ GoodRing
        (N13TwoAdicCoordinateBaseChange.coeffMap a) := by
  change
    N13TwoAdicCoordinateBaseChange.extendCoordinate
        (N13GeneralizedMumfordIntegral.xClass (C a)) =
      N13GeneralizedMumfordIntegral.xClass
        (C (N13TwoAdicCoordinateBaseChange.coeffMap a))
  rw [N13TwoAdicCoordinateBaseChange.extend_xClass]
  simp [N13TwoAdicCoordinateBaseChange.mapPoly,
    N13TwoAdicCoordinateBaseChange.coeffMap]
/-- Inverting the vertical nonzero scalars produces the generalized generic
fibre coordinate ring. -/
theorem goodRing_isLocalization :
    IsLocalization verticalScalars GoodRing := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs := s.property
    change
      ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
        algebraMap R₂ IntegralRing r =
          (s : IntegralRing) at hs
    obtain ⟨r, hr, hs⟩ := hs
    change IsUnit (integralToGood (s : IntegralRing))
    rw [← hs, integralToGood_algebraMap]
    have hr0 :
        N13TwoAdicCoordinateBaseChange.coeffMap r ≠ 0 := by
      change algebraMap R₂ Q₂ r ≠ 0
      simpa using
        (IsFractionRing.injective R₂ Q₂).ne
          (mem_nonZeroDivisors_iff_ne_zero.mp hr)
    exact IsUnit.map (algebraMap Q₂ GoodRing)
      (isUnit_iff_ne_zero.mpr hr0)
  · intro z
    obtain ⟨p, q, d, hp, hq⟩ :=
      IsLocalization.surj₂
        ((nonZeroDivisors R₂).map
          (Polynomial.C : R₂ →+* R₂[X]).toMonoidHom)
        Q₂[X]
        (N13GeneralizedMumfordIntegral.coeff0 z)
        (N13GeneralizedMumfordIntegral.coeffY z)
    obtain ⟨r, hr, hd⟩ := d.property
    change C r = (d : R₂[X]) at hd
    rw [← hd] at hp hq
    rw [Polynomial.algebraMap_def] at hp hq
    have hp0 :
        N13GeneralizedMumfordIntegral.coeff0 z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly p := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hp
    have hq0 :
        N13GeneralizedMumfordIntegral.coeffY z *
            C (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13TwoAdicCoordinateBaseChange.mapPoly q := by
      simpa [N13TwoAdicCoordinateBaseChange.mapPoly,
        N13TwoAdicCoordinateBaseChange.coeffMap,
        N13TwoAdicMumfordTransport.mapPoly,
        N13TwoAdicMumfordTransport.coeffMap] using hq
    let numerator : IntegralRing :=
      N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q *
          N13GeneralizedMumfordIntegral.yClass
    let denominator : verticalScalars :=
      ⟨algebraMap R₂ IntegralRing r,
        ⟨r, hr, rfl⟩⟩
    refine ⟨⟨numerator, denominator⟩, ?_⟩
    change
      z * integralToGood (denominator : IntegralRing) =
        integralToGood numerator
    dsimp only [denominator, numerator]
    rw [← N13GeneralizedMumfordIntegral.recompose z]
    rw [integralToGood_algebraMap]
    unfold integralToGood
    simp only [map_add, map_mul,
      N13TwoAdicCoordinateBaseChange.extend_xClass,
      N13TwoAdicCoordinateBaseChange.extend_yClass]
    have hscalar :
        algebraMap Q₂ GoodRing
            (N13TwoAdicCoordinateBaseChange.coeffMap r) =
          N13GeneralizedMumfordIntegral.xClass
            (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) :=
      rfl
    rw [hscalar]
    have hp' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hp0
    have hq' := congrArg
      (N13GeneralizedMumfordIntegral.xClass (R := Q₂)) hq0
    simp only [
      N13GeneralizedMumfordIntegral.xClass_mul] at hp' hq'
    calc
      (N13GeneralizedMumfordIntegral.xClass
              (N13GeneralizedMumfordIntegral.coeff0 z) +
            N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeffY z) *
              N13GeneralizedMumfordIntegral.yClass) *
            N13GeneralizedMumfordIntegral.xClass
              (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) =
          N13GeneralizedMumfordIntegral.xClass
                (N13GeneralizedMumfordIntegral.coeff0 z) *
              N13GeneralizedMumfordIntegral.xClass
                (C (N13TwoAdicCoordinateBaseChange.coeffMap r)) +
            (N13GeneralizedMumfordIntegral.xClass
                  (N13GeneralizedMumfordIntegral.coeffY z) *
                N13GeneralizedMumfordIntegral.xClass
                  (C (N13TwoAdicCoordinateBaseChange.coeffMap r))) *
              N13GeneralizedMumfordIntegral.yClass := by ring
      _ =
          N13GeneralizedMumfordIntegral.xClass
              (N13TwoAdicCoordinateBaseChange.mapPoly p) +
            N13GeneralizedMumfordIntegral.xClass
                (N13TwoAdicCoordinateBaseChange.mapPoly q) *
              N13GeneralizedMumfordIntegral.yClass := by
            rw [hp', hq']
  · intro x y hxy
    exact
      ⟨1, by
        simpa using
          N13TwoAdicCoordinateBaseChange.extendCoordinate_injective hxy⟩
attribute [local instance] MazurProof.N13IntegralModelContraction.integralRationalAlgebra
end
end MazurProof.N13IntegralModelContraction
end

end

theorem solution : type_of% @MazurProof.N13IntegralModelContraction.goodRing_isLocalization := @MazurProof.N13IntegralModelContraction.goodRing_isLocalization
