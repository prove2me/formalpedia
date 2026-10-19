-- Prove2me | solution 1 for MazurTransfer.Order13InfinityClassDiamondEigenvalue.twice_rho_infinityClass
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:48:53.32707+00:00
-- url     : https://prove2.me/submissions/77bfa78a-5f16-4328-b24f-fc9a127851b1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the infinity torsion difference satisfies 2rho(A)=5A;
the arithmetic conjugate norm kills it and the other norm sends it to 8A.
Named downstream consumer: the SAME represented rational Picard norm
kernel identification.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13CubicPrincipalDivisorAndCuspClassOriginalDataAndCertificatesExplicitPlaceSurjectivityV220261018
import Definitions.Def_MazurTransfer_Order13CubicDiamondOrbitOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
import Theorems.Thm_MazurTransfer_order13_cubic_diamond_orbit_places
import Theorems.Thm_MazurTransfer_Order13ActualInfinityPlaceCenters_infinityPlace_eq_actualPlaceOfPoint
import Theorems.Thm_MazurTransfer_Order13InfinityClassActualNormKernels_actual_rho_eq_field_rho
import Theorems.Thm_MazurTransfer_order13_actual_rational_rho_square_apply
noncomputable section
namespace MazurTransfer.InfinityClassEigenvalueProofHelpers20261018
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicDiamondOrbitValuations Order13CubicActualCuspValuations
open Order13CubicPicardClassRelation Order13InfinityPicardClassOrder
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondPicardEndomorphisms
open Order13PellPrincipalDivisor (positivePlace negativePlace)
local instance infinityClassEigenvalueOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance infinityClassEigenvalueOriginalAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
local notation "σ" => diamondAlgEquiv ℚ

theorem positiveInfinity_eq_positivePlace : positiveInfinity = positivePlace :=
  Order13ActualInfinityPlaceCenters.infinityPlace_eq_actualPlaceOfPoint 1 _
theorem negativeInfinity_eq_negativePlace : negativeInfinity = negativePlace :=
  Order13ActualInfinityPlaceCenters.infinityPlace_eq_actualPlaceOfPoint (-1) _

theorem inverse_diamond_positive : σ⁻¹ • positivePlace = zeroPositivePlace := by
  have h := MazurTransfer.order13_cubic_diamond_orbit_places.1
  rw [firstPositivePlace, positiveInfinity_eq_positivePlace] at h
  exact h

theorem inverse_diamond_negative : σ⁻¹ • negativePlace = zeroNegativePlace := by
  have h := MazurTransfer.order13_cubic_diamond_orbit_places.2.1
  rw [firstNegativePlace, negativeInfinity_eq_negativePlace] at h
  exact h

theorem inverse_square_positive : (σ * σ)⁻¹ • positivePlace = negOnePositivePlace := by
  have h := MazurTransfer.order13_cubic_diamond_orbit_places.2.2.1
  rw [secondPositivePlace, positiveInfinity_eq_positivePlace] at h
  exact h

theorem inverse_square_negative : (σ * σ)⁻¹ • negativePlace = negOneNegativePlace := by
  have h := MazurTransfer.order13_cubic_diamond_orbit_places.2.2.2
  rw [secondNegativePlace, negativeInfinity_eq_negativePlace] at h
  exact h

theorem inverse_diamond_infinity_divisor : Pic0.degZeroSMulHom σ⁻¹ infinityDifferenceDivisor = -zeroDifferenceDivisor := by
  apply Subtype.ext
  change σ⁻¹ • (Finsupp.single negativePlace (1 : ℤ) - Finsupp.single positivePlace 1) =
    -(Finsupp.single zeroPositivePlace 1 - Finsupp.single zeroNegativePlace 1)
  rw [smul_sub, Divisor.smul_single, Divisor.smul_single, inverse_diamond_negative, inverse_diamond_positive]
  abel

theorem inverse_square_infinity_divisor : Pic0.degZeroSMulHom (σ * σ)⁻¹ infinityDifferenceDivisor = -negOneDifferenceDivisor := by
  apply Subtype.ext
  change (σ * σ)⁻¹ • (Finsupp.single negativePlace (1 : ℤ) - Finsupp.single positivePlace 1) =
    -(Finsupp.single negOnePositivePlace 1 - Finsupp.single negOneNegativePlace 1)
  rw [smul_sub, Divisor.smul_single, Divisor.smul_single, inverse_square_negative, inverse_square_positive]
  abel

theorem inverse_diamond_infinity_class : σ⁻¹ • infinityClass = -zeroClass := by
  rw [infinityClass, Pic0.smul_mk, inverse_diamond_infinity_divisor]
  exact map_neg (QuotientAddGroup.mk' _) zeroDifferenceDivisor

theorem inverse_square_infinity_class : (σ * σ)⁻¹ • infinityClass = -negOneClass := by
  rw [infinityClass, Pic0.smul_mk, inverse_square_infinity_divisor]
  exact map_neg (QuotientAddGroup.mk' _) negOneDifferenceDivisor

theorem rho_zeroClass : (rho ℚ) zeroClass = -infinityClass := by
  rw [rho_apply]
  have h := congrArg (fun c : Pic0 ℚ (actualCurveFunctionField ℚ) => σ • c) inverse_diamond_infinity_class
  rw [smul_inv_smul, smul_neg] at h
  exact (neg_injective (by simpa only [neg_neg] using h.symm))

theorem rho_square_negOneClass : ((rho ℚ) ^ 2) negOneClass = -infinityClass := by
  have h := congrArg (fun c : Pic0 ℚ (actualCurveFunctionField ℚ) => (σ * σ) • c) inverse_square_infinity_class
  rw [smul_inv_smul, smul_neg] at h
  have h' : (σ * σ) • negOneClass = -infinityClass := neg_injective (by simpa only [neg_neg] using h.symm)
  rw [rho_pow_apply, pow_two]
  exact h'

theorem zeroClass_eq_rho_sub : zeroClass = (rho ℚ) infinityClass - infinityClass := by
  have h := MazurTransfer.order13_actual_rational_rho_square_apply zeroClass
  rw [Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho] at h
  change (rho ℚ) ((rho ℚ) zeroClass) = (rho ℚ) zeroClass - zeroClass at h
  rw [rho_zeroClass, map_neg] at h
  have h' : (rho ℚ) infinityClass = infinityClass + zeroClass := by
    apply neg_injective
    calc
      -((rho ℚ) infinityClass) = -infinityClass - zeroClass := h
      _ = -(infinityClass + zeroClass) := by abel
  rw [h']
  abel

theorem negOneClass_eq_rho : negOneClass = (rho ℚ) infinityClass := by
  have quadratic (c : Pic0 ℚ (actualCurveFunctionField ℚ)) :
      (rho ℚ) ((rho ℚ) c) = (rho ℚ) c - c := by
    have hq := MazurTransfer.order13_actual_rational_rho_square_apply c
    rw [Order13InfinityClassActualNormKernels.actual_rho_eq_field_rho] at hq
    exact hq
  have h : (rho ℚ) (((rho ℚ) ^ 2) negOneClass) = -negOneClass := by
    change (rho ℚ) ((rho ℚ) ((rho ℚ) negOneClass)) = -negOneClass
    rw [quadratic, quadratic]
    abel
  change (rho ℚ) (((rho ℚ) ^ 2) negOneClass) = -negOneClass at h
  rw [rho_square_negOneClass, map_neg] at h
  exact neg_injective h.symm

end MazurTransfer.InfinityClassEigenvalueProofHelpers20261018
open MazurTransfer MazurTransfer.InfinityClassEigenvalueProofHelpers20261018
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13InfinityPicardClassOrder
open MazurTransfer.Order13CubicPicardClassRelation
open MazurTransfer.Order13FieldDiamondPicardEndomorphisms
local instance sourceInfinityClassEigenvalueFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance sourceInfinityClassEigenvalueAlgebraProvider20261018 : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem solution : (2 : ℤ) • (rho ℚ) infinityClass = (5 : ℤ) • infinityClass := by
  have h := three_zeroClass_sub_negOneClass
  rw [zeroClass_eq_rho_sub, negOneClass_eq_rho] at h
  rw [zsmul_sub] at h
  have h' : (2 : ℤ) • (rho ℚ) infinityClass - (5 : ℤ) • infinityClass = 0 := by
    calc
      _ = ((3 : ℤ) • (rho ℚ) infinityClass - (3 : ℤ) • infinityClass - (rho ℚ) infinityClass) - (2 : ℤ) • infinityClass := by abel
      _ = 0 := by rw [h]; abel
  exact sub_eq_zero.mp h'

#print axioms solution
