-- Prove2me | solution 1 for MazurTransfer.Order13PellPrincipalDivisor.pellDivisor_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T14:30:45.246777+00:00
-- url     : https://prove2.me/submissions/1d131838-f6ec-4545-afb7-69ea9605ac4b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact two-point principal divisor of the explicit Pell
function in the actual rational scheme function field. Named downstream
consumer: nineteen annihilates the difference of the infinity Picard classes.
-/
import Definitions.Def_MazurTransfer_Order13PellPrincipalDivisorData
import Definitions.Def_MazurTransfer_Order13PellChartOverlapIdentities
import Theorems.Thm_MazurTransfer_Order13PellPrincipalDivisor_pellFunction_ord_away_infinity
import Theorems.Thm_MazurTransfer_Order13PellActualOrdinaryChart_pellFunction_eq_ordinaryPlus
noncomputable section
open MazurTransfer
open Order13PellPrincipalDivisor
open AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13IntegralSections Order13RationalSectionPicardInjection Order13ActualInfinityPlaceCenters
open Order13PellActualInfinityValuations
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem solution (v : Place ℚ (actualCurveFunctionField ℚ)) :
    pellDivisor v = v.ord pellFunction := by
  classical
  by_cases hp : v = positivePlace
  · subst v
    simp only [pellDivisor, Finsupp.sub_apply, Finsupp.single_apply,
      if_neg negativePlace_ne_positivePlace, if_pos rfl, zero_sub]
    exact canonical_positive_infinity_pell_ord.symm
  · by_cases hn : v = negativePlace
    · subst v
      simp only [pellDivisor, Finsupp.sub_apply, Finsupp.single_apply,
        if_pos rfl, if_neg negativePlace_ne_positivePlace.symm, sub_zero]
      exact canonical_negative_infinity_pell_ord.symm
    · rw [pellFunction_ord_away_infinity v hp hn]
      simp [pellDivisor, Finsupp.single_apply, hp, hn, Ne.symm hp, Ne.symm hn]


#print axioms solution
