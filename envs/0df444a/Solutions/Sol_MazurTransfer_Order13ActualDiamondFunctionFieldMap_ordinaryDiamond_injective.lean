-- Prove2me | solution 1 for MazurTransfer.Order13ActualDiamondFunctionFieldMap.ordinaryDiamond_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:13:43.006132+00:00
-- url     : https://prove2.me/submissions/e3dd9509-1b7b-460d-a77c-34f730ee0c92

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: injection of the original actual diamond coordinate map.
Named downstream consumer: its extension to the actual rational function field. -/
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryDiamondCoordinateMap
import Theorems.Thm_MazurTransfer_Order13DiamondSexticSymmetry_transcendental_diamondX
noncomputable section
universe u v w
namespace MazurTransfer.Order13DiamondIntegralMapHelpers20261017
theorem injective_of_integral (R : Type u) [CommRing R] [Nontrivial R]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    (B : Type w) [CommRing B] (f : A →+* B)
    (h : Function.Injective (f.comp (algebraMap R A))) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := R)
  change RingHom.ker (f.comp (algebraMap R A)) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp h
end MazurTransfer.Order13DiamondIntegralMapHelpers20261017
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13PellActualOrdinaryChart MazurTransfer.Order13ChartOverlapFunctionField
open MazurTransfer.Order13DiamondSexticSymmetry
open MazurTransfer.Order13ActualOrdinaryPolynomialTranscendence
open MazurTransfer.Order13ActualDiamondFunctionFieldMap
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
theorem solution : Function.Injective ordinaryDiamond := by
  let : Algebra.IsIntegral (Polynomial ℚ) (CoordinateRing ℚ) := ordinary_isIntegral
  apply MazurTransfer.Order13DiamondIntegralMapHelpers20261017.injective_of_integral (Polynomial ℚ) (CoordinateRing ℚ)
    (actualCurveFunctionField ℚ) ordinaryDiamond
  have H : ordinaryDiamond.comp (algebraMap (Polynomial ℚ) (CoordinateRing ℚ)) =
      (aeval (diamondX (xImage ℚ))).toRingHom := by
    apply RingHom.ext
    intro p
    exact ordinaryDiamond_polynomial p
  rw [H]
  exact transcendental_iff_injective.mp (transcendental_diamondX ℚ (xImage ℚ) xImage_transcendental)
#print axioms solution
