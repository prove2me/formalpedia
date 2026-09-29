-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.red_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/35fb28c4-689c-542b-bd14-63de98d89c5e

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_red_surjective
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_red_surjective.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC KroneckerCongruence charLGeomPlaceEquiv charLGeomPlaceOfPoint"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "d4 sp_eq_charLGeomPlaceOfPoint_of_ord_pos sp_eq_placeInfty_of_forall_ord_le_zero"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

include P in

private theorem _root_.ModularCurve.PlaceSpecialization.iac_eq_placeInfty_or_exists (v : Place k (modularFunctionFieldC k 1)) :
    letI := Classical.decEq (RatFunc k)
    v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) ∨
      ∃ a : A, v = charLGeomPlaceOfPoint k (red a) := by
  obtain ⟨w, rfl⟩ := P.d4 v
  by_cases h : ∃ a : A, 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ))
  · obtain ⟨a, ha⟩ := h
    exact Or.inr ⟨a, P.sp_eq_charLGeomPlaceOfPoint_of_ord_pos w a ha⟩
  · push_neg at h
    exact Or.inl (P.sp_eq_placeInfty_of_forall_ord_le_zero w h)

p2m_export "ModularCurve.PlaceSpecialization" "iac_eq_placeInfty_or_exists"
include P in

private theorem _root_.ModularCurve.PlaceSpecialization.iac_ratFunc (v₀ : Place k (RatFunc k)) :
    letI := Classical.decEq (RatFunc k)
    v₀ = RationalFunctionField.placeInfty k ∨ ∃ a : A, v₀ = RationalFunctionField.placeOfPoint k (red a) := by
  rcases P.iac_eq_placeInfty_or_exists (charLGeomPlaceEquiv k v₀) with h | ⟨a, h⟩
  · exact Or.inl ((charLGeomPlaceEquiv k).injective h)
  · exact Or.inr ⟨a, (charLGeomPlaceEquiv k).injective h⟩

p2m_export "ModularCurve.PlaceSpecialization" "iac_ratFunc"

private theorem iac_ofHeightOneSpectrum_ne_placeInfty [DecidableEq (RatFunc k)]
    (w : IsDedekindDomain.HeightOneSpectrum (Polynomial k)) :
    Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) w ≠ RationalFunctionField.placeInfty k := by
  intro h
  have hX : (RatFunc.X : RatFunc k)
      ∈ (Place.ofHeightOneSpectrum (K := k) (F := RatFunc k) w).toValuationSubring := by
    have := RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum k w Polynomial.X
    rwa [RatFunc.algebraMap_X] at this
  rw [h, RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
    RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hX
  norm_num at hX

end ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : Function.Surjective red := by
  letI := Classical.decEq (RatFunc k)
  intro b
  rcases P.iac_ratFunc (RationalFunctionField.placeOfPoint k b) with h | ⟨a, h⟩
  · rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum] at h
    exact absurd h (PlaceSpecialization.iac_ofHeightOneSpectrum_ne_placeInfty _)
  · exact ⟨a, (RationalFunctionField.placeOfPoint_injective k h).symm⟩

end S_ModularCurve_PlaceSpecialization_red_surjective
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_red_surjective (solution)
