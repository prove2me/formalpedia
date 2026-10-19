-- Prove2me | solution 1 for MazurTransfer.Order13InfinityPicardClassOrder.infinityClass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T13:42:39.751989+00:00
-- url     : https://prove2.me/submissions/e18b00b8-49fa-44f8-8f10-874b8485c8e0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original actual infinity divisor class is nonzero.
Named downstream consumer: its exact additive order nineteen.
The statement and actual class constructor are unchanged. This independent
proof uses the public perfect-field genus-zero obstruction directly rather
than the larger rational-section Picard injection dictionary.
-/
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_genusFF_eq_zero_of_principal_single_sub_single
noncomputable section
open MazurTransfer AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13InfinityPicardClassOrder Order13PellPrincipalDivisor
open Order13ActualInfinityPlaceCenters Order13PellActualInfinityValuations
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
theorem solution : infinityClass ≠ 0 := by
  intro hzero
  let f := QuotientAddGroup.mk' ((Divisor.principal (K := ℚ)
    (F := actualCurveFunctionField ℚ)).addSubgroupOf
      (Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)))
  change f infinityDifferenceDivisor = 0 at hzero
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hzero
  change Divisor.IsPrincipal
    (Finsupp.single negativePlace 1 - Finsupp.single positivePlace 1) at hmem
  have hp := infinityPlace_deg 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)
  rw [infinityPlace_eq_actualPlaceOfPoint] at hp
  change positivePlace.deg = 1 at hp
  have hg := RationalPlacePicardInjection.genusFF_eq_zero_of_principal_single_sub_single
    (actual_constantsAreBase_good_characteristic ℚ) negativePlace_ne_positivePlace hp hmem
  rw [actual_genusFF_eq_two_good_characteristic ℚ] at hg
  norm_num at hg
#print axioms solution
