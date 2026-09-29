-- Prove2me | solution 1 for ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/e0a8c9d8-ee79-578c-b999-be36ff39fa62

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SpecializeModuli
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "IsSupersingularPlace ssPlaces jGeomGen jNGeomGen_one IsCentreOf modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint deg_charLGeomPlaceOfPoint ssJSet eq_charLGeomPlaceOfPoint_of_ord_pos"
p2m_open "ModularCurve"

private theorem hwgRatFuncEquivCharLOneC_algebraMap_X (K : Type*) [Field K] :
    ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
      = jGeomGen K 1 := by
  refine Subtype.ext ?_
  rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply,
    RatFunc.algEquivOfTranscendental_algebraMap, Polynomial.aeval_X]
  rfl

private theorem hwgRatFuncEquivCharLOneC_algebraMap_X_sub_C (K : Type*) [Field K] (a : K) :
    ratFuncEquivCharLOneC K
        (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a))
      = jGeomGen K 1 - algebraMap K (modularFunctionFieldC K 1) a := by
  rw [map_sub, map_sub, hwgRatFuncEquivCharLOneC_algebraMap_X]
  congr 1
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
  exact (ratFuncEquivCharLOneC K).commutes a

private theorem hwgOrd_jGeomGen_sub_pos (K : Type*) [Field K] (a : K) :
    0 < (charLGeomPlaceOfPoint K a).ord
      (jGeomGen K 1 - algebraMap K (modularFunctionFieldC K 1) a) := by
  have hmem : algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a) ∈
      (RationalFunctionField.placeOfPoint K a).toValuationSubring := by
    rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
    exact RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K _ _
  have hne : (RationalFunctionField.placeOfPoint K a).ord
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a)) ≠ 0 := by
    rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
    refine (Place.ord_ofHeightOneSpectrum_ne_zero_iff _
      (Polynomial.X_sub_C_ne_zero a)).mpr ?_
    rw [RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal]
    exact Ideal.mem_span_singleton_self _
  have hpop : 0 < (RationalFunctionField.placeOfPoint K a).ord
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a)) :=
    lt_of_le_of_ne ((RationalFunctionField.placeOfPoint K a).ord_nonneg_of_mem hmem)
      (Ne.symm hne)
  have htrans : (charLGeomPlaceOfPoint K a).ord
      (jGeomGen K 1 - algebraMap K (modularFunctionFieldC K 1) a)
      = (RationalFunctionField.placeOfPoint K a).ord
          (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a)) := by
    rw [← hwgRatFuncEquivCharLOneC_algebraMap_X_sub_C K a]
    show (Place.congrRingEquiv (ratFuncEquivCharLOneC K).toRingEquiv
        (fun x => (ratFuncEquivCharLOneC K).commutes x)
        (RationalFunctionField.placeOfPoint K a)).ord
          ((ratFuncEquivCharLOneC K).toRingEquiv
            (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a)))
      = (RationalFunctionField.placeOfPoint K a).ord
          (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C a))
    exact Place.ord_congrRingEquiv _ _ _ _
  rw [htrans]
  exact hpop

private theorem hwgIsCentreOf_charLGeomPlaceOfPoint (K : Type*) [Field K] (a : K) :
    IsCentreOf K 1 (a, a) (charLGeomPlaceOfPoint K a) := by
  constructor
  · exact hwgOrd_jGeomGen_sub_pos K a
  · rw [jNGeomGen_one]
    exact hwgOrd_jGeomGen_sub_pos K a

private theorem hwgIsSupersingularPlace_charLGeomPlaceOfPoint (q : ℕ) (K : Type*)
    [Field K] [DecidableEq K] {a : K} (ha : a ∈ ssJSet q K) :
    IsSupersingularPlace q 1 K (charLGeomPlaceOfPoint K a) := by
  refine ⟨?_, (hwgIsCentreOf_charLGeomPlaceOfPoint K a).isAffineGeomPlace, ?_⟩
  · exact (Place.deg_eq_one_iff_surjective_algebraMap_residueField _).mp
      (deg_charLGeomPlaceOfPoint K a)
  · rw [(hwgIsCentreOf_charLGeomPlaceOfPoint K a).evalAt_jGeomGen]
    exact ha

private theorem hwgMem_ssPlaces_one_iff (q : ℕ) (K : Type*) [Field K] [DecidableEq K]
    (w : Place K (modularFunctionFieldC K 1)) :
    w ∈ ssPlaces q 1 K ↔ ∃ a ∈ ssJSet q K, charLGeomPlaceOfPoint K a = w := by
  constructor
  · intro hw
    have hss : IsSupersingularPlace q 1 K w := hw
    refine ⟨w.evalAt (jGeomGen K 1), hss.2.2, ?_⟩
    exact (ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos hss.isCentreOf_evalAt.1).symm
  · rintro ⟨a, ha, rfl⟩
    exact hwgIsSupersingularPlace_charLGeomPlaceOfPoint q K ha

end ModularCurve

theorem solution (q : ℕ) (K : Type*) [Field K] [DecidableEq K]
    (w : Place K (modularFunctionFieldC K 1)) :
    w ∈ ssPlaces q 1 K ↔ ∃ a ∈ ssJSet q K, charLGeomPlaceOfPoint K a = w :=
  ModularCurve.hwgMem_ssPlaces_one_iff q K w

end

end S_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
end P2MW
export P2MW.S_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq (solution)
