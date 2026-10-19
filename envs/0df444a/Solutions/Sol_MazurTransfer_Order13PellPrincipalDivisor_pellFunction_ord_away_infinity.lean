-- Prove2me | solution 1 for MazurTransfer.Order13PellPrincipalDivisor.pellFunction_ord_away_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:11:52.822989+00:00
-- url     : https://prove2.me/submissions/51f00904-a7b1-4c68-8c9a-2a3fcd934926

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact two-point principal divisor of the explicit Pell
function in the actual rational scheme function field. Named downstream
consumer: nineteen annihilates the difference of the infinity Picard classes.
-/
import Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
import Theorems.Thm_MazurTransfer_Order13OrdinaryChartComplement_point_in_ordinary_or_infinity
import Theorems.Thm_MazurTransfer_Order13PellOrdinaryPlaceOrders_pellFunction_ord_at_ordinary_point
noncomputable section
open MazurTransfer
open Order13PellPrincipalDivisor
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
open Order13PellActualInfinityValuations Order13PellOrdinaryPlaceOrders
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

namespace MazurTransfer.ActualPellAwayInfinityHelpers20261017
theorem pellFunction_ord_at_ordinary_range
    (x : closedPoints (curveScheme ℚ)) (hx : x.1 ∈ (ordinaryChartMap ℚ).opensRange) :
    (actualPlaceOfPoint ℚ x).ord Order13PellActualInfinityValuations.pellFunction = 0 := by
  obtain ⟨p, hp⟩ := hx
  exact pellFunction_ord_at_ordinary_point p x hp

end MazurTransfer.ActualPellAwayInfinityHelpers20261017
open MazurTransfer.ActualPellAwayInfinityHelpers20261017
theorem solution (v : Place ℚ (actualCurveFunctionField ℚ))
    (hp : v ≠ positivePlace) (hn : v ≠ negativePlace) : v.ord pellFunction = 0 := by
  obtain ⟨x, rfl⟩ := (actualPlaceOfPoint_bijective ℚ).2 v
  rcases Order13OrdinaryChartComplement.point_in_ordinary_or_infinity x.1 with hx | hx | hx
  · exact pellFunction_ord_at_ordinary_range x hx
  · exfalso
    apply hp
    congr 1
    apply Subtype.ext
    exact hx.trans (infinity_section_center 1 (Order13PellInfinityLocalOrders.positiveProof ℚ)).symm
  · exfalso
    apply hn
    congr 1
    apply Subtype.ext
    exact hx.trans (infinity_section_center (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ)).symm


#print axioms solution
