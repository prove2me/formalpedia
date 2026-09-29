-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFstSupply_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e09c4280-73ee-57f6-8e62-26ed69f753de

import Mathlib
import Definitions.Def_ModularCurve_LevelOneChartFst
import Definitions.Def_ModularCurve_SmoothPointLocalRing
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_IsModel_exists_hasValue_of_mem_smoothLocalRingFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstSupply_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstSupply_of_isModel.ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair"

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence charLGeomPlaceEquiv mem_ssPlaces_iff jGeomGen jNGeomGen_one IsAffineGeomPlace order_jqModC_def jqModC_ne_zero_def isInftySide_cuspInftyBar frobOnPlacesGeomLevel_charLGeomPlaceOfPoint frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty pow_q_sq_eq_self_of_mem_ssJSet mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg ord_charLGeomPlaceEquiv_placeInfty_eq_order" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.isAffineGeomPlace_one_iff_ne_placeInfty (k : Type*) [Field k] [DecidableEq (RatFunc k)]
    (v : Place k ↥(modularFunctionFieldC k 1)) :
    IsAffineGeomPlace k 1 v ↔ v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  have hne0 : (jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) ≠ 0 := by
    intro h0
    exact jqModC_ne_zero_def k (congrArg Subtype.val h0)
  have hpole : ¬ (jGeomGen k 1 ∈ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).toValuationSubring) := by
    intro hmem
    have hord := (Place.mem_iff_ord_nonneg _ hne0).mp hmem
    rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order] at hord
    have : ((jGeomGen k 1 : ↥(modularFunctionFieldC k 1)) : LaurentSeries k).order = -1 := order_jqModC_def k
    omega
  constructor
  · rintro h rfl
    exact hpole h.1
  · intro hne
    have hmem : jGeomGen k 1 ∈ v.toValuationSubring := by
      by_contra hn
      apply hne
      apply eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
      have h := (not_iff_not.mpr (Place.mem_iff_ord_nonneg v hne0)).mp hn
      exact lt_of_not_ge h
    refine ⟨hmem, ?_⟩
    rw [jNGeomGen_one]
    exact hmem

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel)
    (hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))) (hS₁ : R.ChartFstLaws S₁) :
    R.ChartFstSupply S₁ := by
  classical
  refine
    { sheet := hS₁
      exists_divisor := fun f hf => ?_
      pw_strict := fun W hW f h₁ hfib => hR.exists_hasValue_of_mem_smoothLocalRingFst hW f h₁
        ((R.mem_smoothLocalRingFst_iff _ f).mpr ⟨h₁, hfib⟩)
      pw_cusp := fun W hW f h₁ hr => R.exists_hasValue_of_isInftySide hW f h₁ hr
      div_strict := fun f h₁ hf D hD v hv => ?_
      div_cusp := fun f h₁ hf D hD => ?_
      cusp_fixed := ?_
      redFst_eq_of_isInftySide := fun W hW => ?_
      redFst_eq_charLGeomPlaceOfPoint_iff := fun W c₀ => P.redFst_eq_charLGeomPlaceOfPoint_iff W c₀
      frob_charLGeomPlaceOfPoint := fun a => frobOnPlacesGeomLevel_charLGeomPlaceOfPoint (ResidueField ↥A) data hKr a
      pow_sq_eq_self_of_mem := fun a ha => pow_q_sq_eq_self_of_mem_ssJSet p ha
      isAffineGeomPlace_iff := fun v => ?_
      mem_ssPlaces_iff := fun v => mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq p (ResidueField ↥A) v
      isInftySide_cuspInftyBar := isInftySide_cuspInftyBar P }
  · obtain ⟨D, hD, -⟩ := hPD.exists_divisor f hf
    exact ⟨D, hD⟩
  · convert R.divisorLawFst_oneSided f h₁ hf D hD v hv
  · convert R.cuspLawInfty_oneSided f h₁ hf D hD
  · rw [P.redFst_cuspInftyBar, frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty,
      frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty]
  · rw [P.redFst_eq_placeInfty_of_forall_ord_le_zero W hW.1, P.redFst_cuspInftyBar]
  · rw [P.redFst_cuspInftyBar]
    exact isAffineGeomPlace_one_iff_ne_placeInfty (ResidueField ↥A) v

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstSupply_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFstSupply_of_isModel (solution)
