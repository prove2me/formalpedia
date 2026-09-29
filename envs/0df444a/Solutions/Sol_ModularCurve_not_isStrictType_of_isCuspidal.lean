-- Prove2me | solution 1 for ModularCurve.not_isStrictType_of_isCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4f5126bb-52dd-5f1c-bc35-38aa8e674632

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_not_isStrictType_of_isCuspidal
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_not_isStrictType_of_isCuspidal.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv transcendental_jqModC eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg"
p2m_open "ModularCurve"

theorem ratFuncEquivCharLOneC_X' (k : Type*) [Field k] :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

theorem Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0)
    (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero n hf) hf, ih]; push_cast; ring

theorem frobOnPlacesGeomLevel_placeInfty (k : Type*) [Field k] {q : ℕ} [Fact q.Prime] [CharP k q]
    [DecidableEq (RatFunc k)] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))
      = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  set J : modularFunctionFieldC k 1 := ⟨jqModC k, jqModC_mem k 1⟩ with hJ
  have hX : (ratFuncEquivCharLOneC k) RatFunc.X = J := ratFuncEquivCharLOneC_X' k
  have hJ0 : J ≠ 0 := by
    rw [← hX]; exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k).injective).mpr RatFunc.X_ne_zero

  have hJv : J ∉ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).toValuationSubring := by
    rw [charLGeomPlaceEquiv, Place.congrEquiv_apply, Place.congrRingEquiv_toValuationSubring,
      ValuationSubring.mem_comap, RationalFunctionField.placeInfty_toValuationSubring,
      Valuation.mem_valuationSubring_iff]
    have hsymm : ((ratFuncEquivCharLOneC k).toRingEquiv.symm : modularFunctionFieldC k 1 →+* RatFunc k) J
        = RatFunc.X := by
      rw [← hX]
      exact (ratFuncEquivCharLOneC k).toRingEquiv.symm_apply_apply RatFunc.X
    rw [hsymm, RatFunc.inftyValuation.X, not_le, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr zero_lt_one

  have hJφ : J ∉ (frobOnPlacesGeomLevel k 1 data hKr
      (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))).toValuationSubring := by
    rw [mem_frobOnPlacesGeomLevel_iff, frobeniusGeomLevel_jq]
    intro hpow
    apply hJv
    have hq : 0 < q := (Fact.out : q.Prime).pos
    rw [Place.mem_iff_ord_nonneg _ (pow_ne_zero q hJ0), Place.ord_pow' _ hJ0] at hpow
    rw [Place.mem_iff_ord_nonneg _ hJ0]
    by_contra hneg
    push_neg at hneg
    have : (q : ℤ) * (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord J < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast hq) hneg
    omega

  apply eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
  by_contra hge
  exact hJφ ((Place.mem_iff_ord_nonneg _ hJ0).mpr (not_lt.mp hge))

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "jFun IsCuspidal redFst redSnd IsStrictTypeOne IsStrictTypeTwo d1 sp_eq_placeInfty_of_forall_ord_le_zero"
p2m_open "ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem heckeAlphaBar_j_eq_jFun :
    heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      = jFun (q := q) := by
  apply Subtype.ext
  rw [coe_heckeAlphaBar]
  rfl

theorem forall_ord_restrictAlong_le_zero_of_isCuspidal (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) (b : A) :
    (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα).ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ)) ≤ 0 := by
  have h := hW b
  have hord := W.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ))
  rw [map_sub, AlgHom.commutes, heckeAlphaBar_j_eq_jFun] at hord

  have he : 0 < Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) W := by
    unfold Place.ramificationIndexAlong
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
    haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
    exact Place.ramificationIndex_pos (F := ↥(modularFunctionFieldBar 1)) W
  rw [hord] at h
  by_contra hpos
  push_neg at hpos
  have : (0 : ℤ) < Place.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) W * _ :=
    mul_pos (by exact_mod_cast he) hpos
  exact absurd h (not_le.mpr this)

theorem not_isStrictType_of_isCuspidal' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    ¬ P.IsStrictTypeOne W ∧ ¬ P.IsStrictTypeTwo W := by
  classical
  set vinf := charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) with hv
  have hφ : frobOnPlacesGeomLevel k 1 data hKr vinf = vinf := frobOnPlacesGeomLevel_placeInfty k data hKr
  have h1 : P.redFst W = vinf := by
    have := P.sp_eq_placeInfty_of_forall_ord_le_zero
      (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)
      (forall_ord_restrictAlong_le_zero_of_isCuspidal P W hW)
    simpa [redFst] using this
  have h2 : P.redSnd W = vinf := by
    rcases P.d1 W with h | h
    ·
      apply frobOnPlacesGeomLevel_injective k 1 data hKr
      rw [hφ]
      change P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) at h
      rw [← h, h1]
    ·
      change frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W at h
      rw [← h, h1, hφ]
  refine ⟨fun ht => ht.2 ?_, fun ht => ht.2 ?_⟩
  · rw [h1, hφ, hφ]
  · rw [h2, hφ, hφ]

end PlaceSpecialization

theorem not_isStrictType_of_isCuspidal''
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    ¬ P.IsStrictTypeOne W ∧ ¬ P.IsStrictTypeTwo W :=
  PlaceSpecialization.not_isStrictType_of_isCuspidal' P W hW

end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    ¬ P.IsStrictTypeOne W ∧ ¬ P.IsStrictTypeTwo W :=
  ModularCurve.PlaceSpecialization.not_isStrictType_of_isCuspidal' P W hW

end S_ModularCurve_not_isStrictType_of_isCuspidal
end P2MW
export P2MW.S_ModularCurve_not_isStrictType_of_isCuspidal (solution)
