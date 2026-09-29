-- Prove2me | solution 1 for ModularCurve.not_isStrictType_of_isCuspidalSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f79c60b6-571f-535a-b396-2240f75c3e9b

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_not_isStrictType_of_isCuspidalSnd
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isStrictType_of_isCuspidalSnd.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_congr jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange PlaceSpecialization heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence charLGeomPlaceEquiv coeffMap_qExpand frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jqFun IsCuspidal' redFst redSnd IsStrictTypeOne IsStrictTypeTwo d1 sp_eq_placeInfty_of_forall_ord_le_zero"
p2m_open "ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem heckeBetaBar_j_eq_jqFun_e15 :
    heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      = jqFun (q := q) := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) =
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  rw [coeffEmb, coeffMap_qExpand, qExpand_congr (one_mul q)]

theorem forall_ord_restrictAlong_snd_le_zero_of_isCuspidal'_e15 (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal' W) (b : A) :
    (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ).ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ)) ≤ 0 := by
  have h := hW b
  have hord := W.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ))
  rw [map_sub, AlgHom.commutes, heckeBetaBar_j_eq_jqFun_e15] at hord
  have he : 0 < Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) W := by
    unfold Place.ramificationIndexAlong
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
    haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
    haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
    exact Place.ramificationIndex_pos (F := ↥(modularFunctionFieldBar 1)) W
  rw [hord] at h
  by_contra hpos
  push Not at hpos
  have : (0 : ℤ) < Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) W * _ :=
    mul_pos (by exact_mod_cast he) hpos
  exact absurd h (not_le.mpr this)

theorem not_isStrictType_of_isCuspidal'_e15 (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal' W) :
    ¬ P.IsStrictTypeOne W ∧ ¬ P.IsStrictTypeTwo W := by
  classical
  set vinf := charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) with hv
  have hφ : frobOnPlacesGeomLevel k 1 data hKr vinf = vinf :=
    frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr
  have h2 : P.redSnd W = vinf := by
    have := P.sp_eq_placeInfty_of_forall_ord_le_zero
      (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ)
      (forall_ord_restrictAlong_snd_le_zero_of_isCuspidal'_e15 P W hW)
    simpa [redSnd] using this
  have h1 : P.redFst W = vinf := by
    rcases P.d1 W with h | h
    ·
      change P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) at h
      rw [h, h2, hφ]
    ·
      apply frobOnPlacesGeomLevel_injective k 1 data hKr
      change frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W at h
      rw [h, h2, hφ]
  refine ⟨fun ht => ht.2 ?_, fun ht => ht.2 ?_⟩
  · rw [h1, hφ, hφ]
  · rw [h2, hφ, hφ]

end PlaceSpecialization
end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal' W) :
    ¬ P.IsStrictTypeOne W ∧ ¬ P.IsStrictTypeTwo W :=
  ModularCurve.PlaceSpecialization.not_isStrictType_of_isCuspidal'_e15 P W hW

end S_ModularCurve_not_isStrictType_of_isCuspidalSnd
end P2MW
export P2MW.S_ModularCurve_not_isStrictType_of_isCuspidalSnd (solution)
