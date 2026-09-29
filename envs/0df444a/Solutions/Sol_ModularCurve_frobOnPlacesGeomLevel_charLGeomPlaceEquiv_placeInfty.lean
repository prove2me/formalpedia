-- Prove2me | solution 1 for ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e051709c-f82f-5497-bb61-adb086dfaa39

import Mathlib
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty.ModularCurve"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff jqModC modularFunctionFieldC jqModC_mem ModularPolynomialData KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv transcendental_jqModC eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg"
p2m_open "ModularCurve"
variable (k : Type*) [Field k]

private theorem pin_ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

private theorem pin_ord_charLGeomPlaceEquiv (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

private theorem pin_ord_jt_placeInfty_neg [DecidableEq (RatFunc k)] :
    (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)) < 0 := by
  rw [← pin_ratFuncEquivCharLOneC_X, pin_ord_charLGeomPlaceEquiv]
  by_contra hge
  push_neg at hge
  have hmem := Place.mem_of_ord_nonneg _ (RatFunc.X_ne_zero (K := k)) hge
  rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
    RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
  exact absurd hmem (by norm_num)

end ModularCurve
end

theorem solution
    (k : Type*) [Field k] [DecidableEq (RatFunc k)] {q : ℕ} [Fact q.Prime] [CharP k q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k))
      = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  set inf := charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) with hinf
  set J : modularFunctionFieldC k 1 := ⟨jqModC k, jqModC_mem k 1⟩ with hJ
  have hneg : inf.ord J < 0 := ModularCurve.pin_ord_jt_placeInfty_neg k
  have hJ0 : J ≠ 0 := by
    rintro h
    rw [h, Place.ord_zero] at hneg
    exact lt_irrefl _ hneg
  apply ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
  by_contra hge
  push_neg at hge
  have hmem : J ∈ (frobOnPlacesGeomLevel k 1 data hKr inf).toValuationSubring :=
    Place.mem_of_ord_nonneg _ hJ0 hge
  rw [mem_frobOnPlacesGeomLevel_iff, hJ, frobeniusGeomLevel_jq] at hmem
  have h2 : 0 ≤ inf.ord (J ^ q) := Place.ord_nonneg_of_mem _ hmem
  rw [← zpow_natCast, Place.ord_zpow] at h2
  have hq : (0 : ℤ) < (q : ℤ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have h3 : 0 ≤ inf.ord J := le_of_mul_le_mul_left (by simpa using h2) hq
  exact absurd hneg (not_lt.mpr h3)

end S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
end P2MW
export P2MW.S_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty (solution)
