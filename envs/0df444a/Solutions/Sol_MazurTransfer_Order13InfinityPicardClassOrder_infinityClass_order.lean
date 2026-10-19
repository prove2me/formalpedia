-- Prove2me | solution 1 for MazurTransfer.Order13InfinityPicardClassOrder.infinityClass_order
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:44:39.629307+00:00
-- url     : https://prove2.me/submissions/f8bf5820-b337-47c2-8496-7b750a33bb6d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit principal divisor makes the nonzero difference
of the actual infinity section classes an element of exact order nineteen.
Named downstream consumer: the lower bound matching the rational arithmetic
Picard torsion bound from the two good reductions.
-/
import Definitions.Def_MazurTransfer_Order13InfinityDivisorClassData
import Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellDivisor_isPrincipal
import Theorems.Thm_MazurTransfer_Order13InfinityPicardClassOrder_infinityClass_ne_zero
noncomputable section
open MazurTransfer
open Order13InfinityPicardClassOrder
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection
open Order13PellPrincipalDivisor Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

namespace MazurTransfer.ActualInfinityClassOrderHelpers20261017
theorem nineteen_divisor_eq_pellDivisor :
    (((19 : ℤ) • infinityDifferenceDivisor : Divisor.degZero (K := ℚ)
      (F := actualCurveFunctionField ℚ)) : Divisor ℚ (actualCurveFunctionField ℚ)) = pellDivisor := by
  change (19 : ℤ) • (Finsupp.single negativePlace 1 - Finsupp.single positivePlace 1) = _
  simp [pellDivisor, smul_sub, Finsupp.smul_single]

theorem nineteen_smul_infinityClass : (19 : ℤ) • infinityClass = 0 := by
  let f := QuotientAddGroup.mk' ((Divisor.principal (K := ℚ) (F := actualCurveFunctionField ℚ)).addSubgroupOf
    (Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)))
  have Hmem : (19 : ℤ) • infinityDifferenceDivisor ∈
      (Divisor.principal (K := ℚ) (F := actualCurveFunctionField ℚ)).addSubgroupOf
        (Divisor.degZero (K := ℚ) (F := actualCurveFunctionField ℚ)) := by
    change (((19 : ℤ) • infinityDifferenceDivisor : Divisor.degZero (K := ℚ)
      (F := actualCurveFunctionField ℚ)) : Divisor ℚ (actualCurveFunctionField ℚ)) ∈ Divisor.principal
    rw [nineteen_divisor_eq_pellDivisor]
    exact pellDivisor_isPrincipal
  have H : f ((19 : ℤ) • infinityDifferenceDivisor) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr Hmem
  rw [map_zsmul] at H
  exact H


end MazurTransfer.ActualInfinityClassOrderHelpers20261017
open MazurTransfer.ActualInfinityClassOrderHelpers20261017
theorem solution : addOrderOf infinityClass = 19 := by
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  apply addOrderOf_eq_prime
  · exact (natCast_zsmul infinityClass 19).symm.trans nineteen_smul_infinityClass
  · exact infinityClass_ne_zero

#print axioms solution
