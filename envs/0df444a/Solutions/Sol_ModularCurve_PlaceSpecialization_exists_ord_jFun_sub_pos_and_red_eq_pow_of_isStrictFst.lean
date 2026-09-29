-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/878e6295-6e42-5984-898c-627f2db68a69

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
import Theorems.Thm_ModularCurve_heckeBetaBar_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

namespace BranchC

variable {p : ℕ} [Fact p.Prime]

theorem qExpand_congr {m n : ℕ} [NeZero m] [NeZero n] (h : m = n) (x : LaurentSeries ℚ) :
    qExpand ℚ m x = qExpand ℚ n x := by
  subst h; rfl

theorem heckeBetaBar_j_eq_jqFun :
    heckeBetaBar (AlgebraicClosure ℚ) 1 p (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) =
      PlaceSpecialization.jqFun (q := p) := by
  apply Subtype.ext
  rw [heckeBetaBar_coeffEmb (L := (AlgebraicClosure ℚ)) 1 p (modularFunctionField_le_full 1 (jq_mem 1))]
  exact congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_congr (one_mul p).symm jq)

end BranchC

open BranchC in
set_option maxHeartbeats 1600000 in

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hV : P.IsStrictFst V) :
    ∃ a b : A,
      0 < V.ord (PlaceSpecialization.jFun (q := p) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : (AlgebraicClosure ℚ))) ∧
      0 < V.ord (PlaceSpecialization.jqFun (q := p) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : (AlgebraicClosure ℚ))) ∧
      red b = red a ^ p ∧ red a ^ (p ^ 2) ≠ red a := by
  classical
  obtain ⟨h1, h2⟩ := hV
  change frobOnPlacesGeomLevel k 1 data hKr (P.redFst V) = P.redSnd V at h1
  change frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst V)) ≠ P.redFst V at h2
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty k (P.redFst V) with ⟨c₀, hc₀⟩ | hinf
  · obtain ⟨a, hra, ha⟩ := (redFst_eq_charLGeomPlaceOfPoint_iff P V c₀).mp hc₀
    obtain ⟨b, hb⟩ := exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos P V a ha
    have hsnd : P.redSnd V = charLGeomPlaceOfPoint k (red b) :=
      redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos P V b (by rw [heckeBetaBar_j_eq_jqFun]; exact hb)
    rw [hc₀, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, hsnd] at h1
    rw [hc₀, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint] at h2
    have hb' : red b = c₀ ^ p := (charLGeomPlaceOfPoint_injective k h1).symm
    refine ⟨a, b, ha, hb, by rw [hb', hra], fun h => h2 ?_⟩
    rw [← pow_mul, ← sq, ← hra, h]
  · exfalso
    apply h2
    rw [hinf, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty]

end S_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst (solution)
