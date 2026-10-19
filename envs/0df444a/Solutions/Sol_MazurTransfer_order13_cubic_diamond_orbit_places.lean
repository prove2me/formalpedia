-- Prove2me | solution 1 for MazurTransfer.order13_cubic_diamond_orbit_places
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:42:29.326438+00:00
-- url     : https://prove2.me/submissions/26964e6d-0494-4ba3-9774-8ee743837933

import Mathlib
import Definitions.Def_MazurTransfer_Order13CubicPrincipalDivisorAndCuspClassOriginalDataAndCertificatesExplicitPlaceSurjectivityV220261018
import Definitions.Def_MazurTransfer_Order13CubicDiamondOrbitOriginalDataAndCertificates20261018
import Definitions.Def_MazurTransfer_Order13FieldDiamondExactOrderData
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the four original inverse-diamond orbit places of the actual infinity places equal the four named ordinary cusp places. Named downstream consumer: the infinity-class diamond eigenvalue. The twenty-three original place-order and hyperelliptic-action proof helpers are retained under a fresh proof-only namespace, with complete original types audited separately.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the nonzero cubic orders identify the four finite cusp
places and both infinity poles uniquely. Named downstream consumer:
diamond-place action on the cusp differences.
-/

noncomputable section
namespace MazurTransfer.CubicPlaceActionProofHelpers20261018.Characterization
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicActualInfinityValuations Order13CubicActualCuspValuations
open Order13CubicMarkedPlaceOrders Order13CubicPrincipalDivisors
open Order13CubicDiamondOrbitValuations
open Order13PellPrincipalDivisor (positivePlace negativePlace)
local instance cubicPlaceActionCharacterizationOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem minus_order_three_identifies_place (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v.ord cubicMinusFunction = 3) : v = zeroPositivePlace := by
  have hrange : v ∈ Set.range markedPlace := by
    by_contra h
    have hz := (cubicFunctions_ord_away_range v h).1
    rw [hv] at hz
    norm_num at hz
  obtain ⟨i, rfl⟩ := hrange
  have hi := markedPlace_minus_order i
  rw [hv] at hi
  fin_cases i <;> norm_num [minusOrders] at hi
  all_goals rfl

theorem minus_order_one_identifies_place (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v.ord cubicMinusFunction = 1) : v = negOneNegativePlace := by
  have hrange : v ∈ Set.range markedPlace := by
    by_contra h
    have hz := (cubicFunctions_ord_away_range v h).1
    rw [hv] at hz
    norm_num at hz
  obtain ⟨i, rfl⟩ := hrange
  have hi := markedPlace_minus_order i
  rw [hv] at hi
  fin_cases i <;> norm_num [minusOrders] at hi
  all_goals rfl

theorem minus_order_negative_one_identifies_place (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v.ord cubicMinusFunction = -1) : v = positivePlace := by
  have hrange : v ∈ Set.range markedPlace := by
    by_contra h
    have hz := (cubicFunctions_ord_away_range v h).1
    rw [hv] at hz
    norm_num at hz
  obtain ⟨i, rfl⟩ := hrange
  have hi := markedPlace_minus_order i
  rw [hv] at hi
  fin_cases i <;> norm_num [minusOrders] at hi
  all_goals rfl

theorem minus_order_negative_three_identifies_place (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v.ord cubicMinusFunction = -3) : v = negativePlace := by
  have hrange : v ∈ Set.range markedPlace := by
    by_contra h
    have hz := (cubicFunctions_ord_away_range v h).1
    rw [hv] at hz
    norm_num at hz
  obtain ⟨i, rfl⟩ := hrange
  have hi := markedPlace_minus_order i
  rw [hv] at hi
  fin_cases i <;> norm_num [minusOrders] at hi
  all_goals rfl

theorem plus_order_three_identifies_place (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v.ord cubicPlusFunction = 3) : v = zeroNegativePlace := by
  have hrange : v ∈ Set.range markedPlace := by
    by_contra h
    have hz := (cubicFunctions_ord_away_range v h).2
    rw [hv] at hz
    norm_num at hz
  obtain ⟨i, rfl⟩ := hrange
  have hi := markedPlace_plus_order i
  rw [hv] at hi
  fin_cases i <;> norm_num [plusOrders] at hi
  all_goals rfl

theorem plus_order_one_identifies_place (v : Place ℚ (actualCurveFunctionField ℚ))
    (hv : v.ord cubicPlusFunction = 1) : v = negOnePositivePlace := by
  have hrange : v ∈ Set.range markedPlace := by
    by_contra h
    have hz := (cubicFunctions_ord_away_range v h).2
    rw [hv] at hz
    norm_num at hz
  obtain ⟨i, rfl⟩ := hrange
  have hi := markedPlace_plus_order i
  rw [hv] at hi
  fin_cases i <;> norm_num [plusOrders] at hi
  all_goals rfl

theorem firstPositivePlace_eq_zeroPositive : firstPositivePlace = zeroPositivePlace :=
  minus_order_three_identifies_place _ cubicMinusFunction_ord_firstPositive

theorem secondNegativePlace_eq_negOneNegative : secondNegativePlace = negOneNegativePlace :=
  minus_order_one_identifies_place _ cubicMinusFunction_ord_secondNegative

end MazurTransfer.CubicPlaceActionProofHelpers20261018.Characterization
#print axioms MazurTransfer.CubicPlaceActionProofHelpers20261018.Characterization.firstPositivePlace_eq_zeroPositive
#print axioms MazurTransfer.CubicPlaceActionProofHelpers20261018.Characterization.secondNegativePlace_eq_negOneNegative

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the diamond cube swaps the literal cusp branches, and
all four inverse-diamond orbit places identify with the named cusp places.
Named downstream consumer: the actual infinity-class diamond eigenvalue.
-/

noncomputable section
namespace MazurTransfer.CubicPlaceActionProofHelpers20261018.Action
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondExactOrder
open Order13CubicActualInfinityValuations Order13CubicActualOrdinaryChart
open Order13CubicActualCuspValuations Order13CubicMarkedPlaceOrders
open Order13CubicDiamondOrbitValuations CubicPlaceActionProofHelpers20261018.Characterization
open Order13PellPrincipalDivisor (positivePlace negativePlace)
open Order13ActualInfinityPlaceCenters
local instance cubicPlaceActionActionOriginalFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local notation "σ" => diamondAlgEquiv ℚ

theorem cube_inverse : (σ ^ 3)⁻¹ = σ ^ 3 := by
  have h : σ ^ 3 * σ ^ 3 = 1 := by
    rw [← pow_add]
    exact diamondAlgEquiv_pow_six ℚ
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem cube_minus : (σ ^ 3) cubicMinusFunction = -cubicPlusFunction := by
  rw [cubicMinusFunction_eq, cubicPlusFunction_eq]
  change diamondThird ℚ (yImage ℚ - Order13CubicNormChartCertificate.cubic (xImage ℚ)) = _
  simp only [Order13CubicNormChartCertificate.cubic, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
    diamondThird_x, diamondThird_y]
  ring

theorem cube_plus : (σ ^ 3) cubicPlusFunction = -cubicMinusFunction := by
  rw [cubicMinusFunction_eq, cubicPlusFunction_eq]
  change diamondThird ℚ (yImage ℚ + Order13CubicNormChartCertificate.cubic (xImage ℚ)) = _
  simp only [Order13CubicNormChartCertificate.cubic, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
    diamondThird_x, diamondThird_y]
  ring

theorem ord_cube_minus (v : Place ℚ (actualCurveFunctionField ℚ)) :
    (σ ^ 3 • v).ord cubicMinusFunction = v.ord cubicPlusFunction := by
  have h := ord_inverse_smul (σ ^ 3) v cubicMinusFunction
  rw [cube_inverse, cube_minus] at h
  simpa only [Place.ord, Valuation.map_neg] using h

theorem ord_cube_plus (v : Place ℚ (actualCurveFunctionField ℚ)) :
    (σ ^ 3 • v).ord cubicPlusFunction = v.ord cubicMinusFunction := by
  have h := ord_inverse_smul (σ ^ 3) v cubicPlusFunction
  rw [cube_inverse, cube_plus] at h
  simpa only [Place.ord, Valuation.map_neg] using h

theorem cube_positivePlace : σ ^ 3 • positivePlace = negativePlace := by
  apply minus_order_negative_three_identifies_place
  rw [ord_cube_minus]
  exact positivePlace_ord_plus

theorem cube_negativePlace : σ ^ 3 • negativePlace = positivePlace := by
  apply minus_order_negative_one_identifies_place
  rw [ord_cube_minus]
  exact negativePlace_ord_plus

theorem cube_zeroPositivePlace : σ ^ 3 • zeroPositivePlace = zeroNegativePlace := by
  apply plus_order_three_identifies_place
  rw [ord_cube_plus]
  exact cubicMinusFunction_ord_at_zeroPositive

theorem cube_zeroNegativePlace : σ ^ 3 • zeroNegativePlace = zeroPositivePlace := by
  apply minus_order_three_identifies_place
  rw [ord_cube_minus]
  exact cubicPlusFunction_ord_at_zeroNegative

theorem cube_negOneNegativePlace : σ ^ 3 • negOneNegativePlace = negOnePositivePlace := by
  apply plus_order_one_identifies_place
  rw [ord_cube_plus]
  exact cubicMinusFunction_ord_at_negOneNegative

theorem cube_negOnePositivePlace : σ ^ 3 • negOnePositivePlace = negOneNegativePlace := by
  apply minus_order_one_identifies_place
  rw [ord_cube_minus]
  exact cubicPlusFunction_ord_at_negOnePositive

theorem positiveInfinity_eq_positivePlace : positiveInfinity = positivePlace :=
  infinityPlace_eq_actualPlaceOfPoint 1 _
theorem negativeInfinity_eq_negativePlace : negativeInfinity = negativePlace :=
  infinityPlace_eq_actualPlaceOfPoint (-1) _

theorem firstNegativePlace_eq_zeroNegative : firstNegativePlace = zeroNegativePlace := by
  have hcomm : σ ^ 3 * σ⁻¹ = σ⁻¹ * σ ^ 3 := by group
  have h : σ ^ 3 • firstPositivePlace = firstNegativePlace := by
    rw [firstPositivePlace, firstNegativePlace, positiveInfinity_eq_positivePlace, negativeInfinity_eq_negativePlace,
      smul_smul, hcomm, ← smul_smul, cube_positivePlace]
  rw [firstPositivePlace_eq_zeroPositive, cube_zeroPositivePlace] at h
  exact h.symm

theorem secondPositivePlace_eq_negOnePositive : secondPositivePlace = negOnePositivePlace := by
  have hcomm : σ ^ 3 * (σ * σ)⁻¹ = (σ * σ)⁻¹ * σ ^ 3 := by group
  have h : σ ^ 3 • secondNegativePlace = secondPositivePlace := by
    rw [secondNegativePlace, secondPositivePlace, positiveInfinity_eq_positivePlace, negativeInfinity_eq_negativePlace,
      smul_smul, hcomm, ← smul_smul, cube_negativePlace]
  rw [secondNegativePlace_eq_negOneNegative, cube_negOneNegativePlace] at h
  exact h.symm

end MazurTransfer.CubicPlaceActionProofHelpers20261018.Action
#print axioms MazurTransfer.CubicPlaceActionProofHelpers20261018.Action.cube_positivePlace
#print axioms MazurTransfer.CubicPlaceActionProofHelpers20261018.Action.firstNegativePlace_eq_zeroNegative
#print axioms MazurTransfer.CubicPlaceActionProofHelpers20261018.Action.secondPositivePlace_eq_negOnePositive

open MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicDiamondOrbitValuations Order13CubicActualCuspValuations
local instance sourceCubicDiamondOrbitPlacesFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution :
    firstPositivePlace = zeroPositivePlace ∧
      firstNegativePlace = zeroNegativePlace ∧
      secondPositivePlace = negOnePositivePlace ∧
      secondNegativePlace = negOneNegativePlace := by
  exact ⟨CubicPlaceActionProofHelpers20261018.Characterization.firstPositivePlace_eq_zeroPositive,
    CubicPlaceActionProofHelpers20261018.Action.firstNegativePlace_eq_zeroNegative,
    CubicPlaceActionProofHelpers20261018.Action.secondPositivePlace_eq_negOnePositive,
    CubicPlaceActionProofHelpers20261018.Characterization.secondNegativePlace_eq_negOneNegative⟩
#print axioms solution
