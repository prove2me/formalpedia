-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ff9fa643-0c23-5592-8189-58f76d29bc1f

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
import Theorems.Thm_ModularCurve_MultCovering_neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase"
p2m_attr_erase "instance" "instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective jWidth jWidth_eq_one_or exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord MultCovering.mem_zeroChart_nodes_iff ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap ord_charLGeomPlaceEquiv_placeInfty_jqModC"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "hasseExp goodFamilyZero FamCtx mAnnuli ChartCtx zeroChart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq nodeSrc AnnCtx hasseExp_le_two_of_thirteen_le neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero hasseExp_zero eq_mAnnuli_add_one_of_isEmbBasis mem_zeroChart_nodes_iff zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes"
p2m_open "ModularCurve.MultCovering ModularCurve"
section TwoContentTwo

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA Δ in

theorem card_filter_hasseExp_le_one_le_card_widthOne_add_one
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    (Finset.univ.filter (fun l : Fin r => hasseExp Φ.toFamData l ≤ 1)).card
      ≤ (Finset.univ.filter (fun e : Fin (mAnnuli p) => jWidth (ssValue Γ e) = 1)).card + 1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : DecidableEq (RatFunc (ResidueField ↥A)) := Classical.decEq _
  set res₀ : Fin r → ↥(modularFunctionFieldC (ResidueField ↥A) 1) :=
    fun l => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ with hres₀
  set jB : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ with hjB
  set S : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => jWidth (ssValue Γ e) = 1) with hS
  set S₀ : Finset (ResidueField ↥A) := S.image (fun e => ssValue Γ e ^ p) with hS₀
  have hS₀card : S₀.card = S.card := by
    refine Finset.card_image_of_injective _ ?_
    intro e e' h
    apply ssValue_injective Γ
    exact frobenius_inj (ResidueField ↥A) p h
  have hmemS₀ : ∀ {b : ResidueField ↥A}, b ∈ S₀ ↔ ∃ e, jWidth (ssValue Γ e) = 1 ∧ ssValue Γ e ^ p = b := by
    intro b
    simp only [hS₀, hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  have hnodes : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∈ (zeroChart Γ).nodes ↔ ∃ e, charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e ^ p) = v := by
    intro v
    rw [ModularCurve.MultCovering.mem_zeroChart_nodes_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
      exact ⟨e, by rw [he]⟩
    · rintro ⟨e, rfl⟩
      exact ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, rfl⟩
  have hnodeSrc : ∀ e, nodeSrc Γ e = charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e ^ p) := fun e => rfl
  have hinf_not : charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A)) ∉ (zeroChart Γ).nodes := by
    intro hmem
    obtain ⟨e, he⟩ := (hnodes _).mp hmem
    have h1 := ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (ResidueField ↥A)
    have h2 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (ResidueField ↥A) (ssValue Γ e ^ p) 0
    rw [map_zero, sub_zero, he] at h2
    rw [h2] at h1
    split_ifs at h1 <;> omega
  set T : Finset (Fin r) := Finset.univ.filter (fun l => hasseExp Φ.toFamData l ≤ 1) with hT
  have hpres : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      (∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord g) →
      (∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord g) →
      ∃ Q : Polynomial (ResidueField ↥A), Q ∈ Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) ∧
        (∏ a ∈ S₀, (jB - algebraMap (ResidueField ↥A) _ a)) * g = Polynomial.aeval jB Q := by
    intro g hg hgn
    have hreg' : ∀ b : ResidueField ↥A, b ∉ S₀ → 0 ≤ (charLGeomPlaceOfPoint (ResidueField ↥A) b).ord g := by
      intro b hb
      by_cases hbn : charLGeomPlaceOfPoint (ResidueField ↥A) b ∈ (zeroChart Γ).nodes
      · obtain ⟨e, he⟩ := (hnodes _).mp hbn
        have hw : jWidth (ssValue Γ e) ≠ 1 := by
          intro hw; exact hb (hmemS₀.mpr ⟨e, hw, by
            exact charLGeomPlaceOfPoint_injective (ResidueField ↥A) (by simpa using he)⟩)
        have := hgn e
        rw [hnodeSrc, he] at this
        have hdiv : (1 / jWidth (ssValue Γ e) : ℕ) = 0 := by
          rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h
          · exact absurd h hw
          · rw [h]
          · rw [h]
        rw [hdiv] at this
        simpa using this
      · exact hg _ hbn
    have hS₀' : ∀ a ∈ S₀, -1 ≤ (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord g := by
      intro a ha
      obtain ⟨e, hw, rfl⟩ := hmemS₀.mp ha
      have := hgn e
      rw [hw, hnodeSrc] at this
      simpa using this
    have hinf' : -((0 : ℕ) : ℤ) ≤ (charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A))).ord g := by
      simpa using hg _ hinf_not
    obtain ⟨Q, hQdeg, hQ⟩ := ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
      S₀ 0 g hreg' hS₀' hinf'
    refine ⟨Q, ?_, hQ⟩
    rw [Polynomial.mem_degreeLT]
    by_cases hQ0 : Q = 0
    · rw [hQ0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have := hQdeg hQ0
      rw [zero_add] at this
      exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le this)
  have hT_reg : ∀ l ∈ T, ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord (res₀ l) := by
    intro l _ v hv
    obtain ⟨hint', hz3⟩ := zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p A hA Γ Φ
    exact hz3 l v hv
  have hT_node : ∀ l ∈ T, ∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord (res₀ l) := by
    intro l hl e
    have hn : hasseExp Φ.toFamData l ≤ 1 := (Finset.mem_filter.mp hl).2
    obtain ⟨hint', hb⟩ :=
      neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero p A hA Γ Δ Φ
    have hb' : -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord (res₀ l) := hb e l
    have hdiv : hasseExp Φ.toFamData l / jWidth (ssValue Γ e) ≤ 1 / jWidth (ssValue Γ e) :=
      Nat.div_le_div_right hn
    omega
  have hQT : ∀ l : T, ∃ Q : Polynomial (ResidueField ↥A), Q ∈ Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) ∧
      (∏ a ∈ S₀, (jB - algebraMap (ResidueField ↥A) _ a)) * res₀ l = Polynomial.aeval jB Q :=
    fun l => hpres (res₀ l) (hT_reg l l.2) (hT_node l l.2)
  choose QT hQT_mem hQT_eq using hQT
  set D : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := ∏ a ∈ S₀, (jB - algebraMap (ResidueField ↥A) _ a) with hD
  have hD0 : D ≠ 0 := by
    rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
    intro h0
    have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (ResidueField ↥A) a a
    rw [if_pos rfl] at h1
    change (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord (jB - algebraMap (ResidueField ↥A) _ a) = 1 at h1
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hQTLI : LinearIndependent (ResidueField ↥A) (fun l : T => (⟨QT l, hQT_mem l⟩ : Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 := congrArg (fun x : Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) => Polynomial.aeval jB (x : Polynomial (ResidueField ↥A))) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, ZeroMemClass.coe_zero, map_zero] at h1
    have e2 : ∀ l : T, g l • Polynomial.aeval jB (QT l) = D * (g l • res₀ l) := by
      intro l; rw [← hQT_eq l, mul_smul_comm]
    simp only [e2] at h1
    rw [← Finset.mul_sum] at h1
    have hsum : ∑ l : T, g l • res₀ l = 0 := (mul_eq_zero.mp h1).resolve_left hD0
    have hLI' := hLI.comp (fun l : T => (l : Fin r)) Subtype.val_injective
    exact (Fintype.linearIndependent_iff.mp hLI') g hsum l
  have hTle : T.card ≤ S.card + 1 := by
    have := hQTLI.fintype_card_le_finrank
    rw [Fintype.card_coe, LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv (ResidueField ↥A) (S₀.card + 1)),
      Module.finrank_fin_fun, hS₀card] at this
    exact this
  exact hTle

include hA Δ in

theorem exists_ne_hasseExp_eq_two_of_jWidth_ne_one' (hp13 : 13 ≤ p)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∀ e₁ e₂ : Fin (mAnnuli p), e₁ ≠ e₂ → jWidth (ssValue Γ e₁) ≠ 1 → jWidth (ssValue Γ e₂) ≠ 1 →
      ∃ l₂ l₃ : Fin r, l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
        hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 2 := by
  intro e₁ e₂ hne hw₁ hw₂
  have hp5 : 5 ≤ p := le_trans (by norm_num) hp13
  set S : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => jWidth (ssValue Γ e) = 1) with hS
  set T : Finset (Fin r) := Finset.univ.filter (fun l => hasseExp Φ.toFamData l ≤ 1) with hT
  set Tc : Finset (Fin r) := Finset.univ.filter (fun l => 2 ≤ hasseExp Φ.toFamData l) with hTc
  have hTle : T.card ≤ S.card + 1 :=
    card_filter_hasseExp_le_one_le_card_widthOne_add_one p A hA Γ Δ Φ hint hLI

  have hS2 : S.card + 2 ≤ mAnnuli p := by
    have h21 : e₂ ∈ Finset.univ.erase e₁ := Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩
    have hsub : S ⊆ (Finset.univ.erase e₁).erase e₂ := by
      intro e he
      have hw : jWidth (ssValue Γ e) = 1 := (Finset.mem_filter.mp he).2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
      · rintro rfl; exact hw₂ hw
      · rintro rfl; exact hw₁ hw
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem h21, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin] at hc
    have hm2 : 2 ≤ mAnnuli p := by
      have := Finset.card_le_univ ({e₁, e₂} : Finset (Fin (mAnnuli p)))
      rwa [Finset.card_pair hne, Fintype.card_fin] at this
    omega

  have hr : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 Φ.t Φ.t_basis
  have hpart : T.card + Tc.card = r := by
    have : Tc = Tᶜ := by
      ext l; simp [hT, hTc]; omega
    rw [this, Finset.card_add_card_compl, Fintype.card_fin]
  have hTc2 : 1 < Tc.card := by omega
  obtain ⟨l₂, hl₂, l₃, hl₃, hne'⟩ := Finset.one_lt_card.mp hTc2
  have hmem : ∀ l ∈ Tc, 1 ≤ (l : ℕ) ∧ hasseExp Φ.toFamData l = 2 := by
    intro l hl
    have h2 : 2 ≤ hasseExp Φ.toFamData l := (Finset.mem_filter.mp hl).2
    have h3 := hasseExp_le_two_of_thirteen_le p hp13 A hA Γ Δ Φ l
    refine ⟨?_, le_antisymm h3 h2⟩
    by_contra h0
    have h00 := hasseExp_zero Φ l (by omega)
    omega
  exact ⟨l₂, l₃, hne', (hmem l₂ hl₂).1, (hmem l₃ hl₃).1, (hmem l₂ hl₂).2, (hmem l₃ hl₃).2⟩

end TwoContentTwo
end ModularCurve.MultCovering

open AlgebraicCurve IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one.ModularCurve _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one.ModularCurve.MultCovering in
theorem solution (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∀ e₁ e₂ : Fin (mAnnuli p), e₁ ≠ e₂ → jWidth (ssValue Γ e₁) ≠ 1 → jWidth (ssValue Γ e₂) ≠ 1 →
      ∃ l₂ l₃ : Fin r, l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
        hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 2 :=
  ModularCurve.MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one' p A hA Γ Δ Φ hp13 hint hLI

end S_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one (solution)
