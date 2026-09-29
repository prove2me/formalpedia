-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_hasseExp_eq_one_unramified_and_separates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9b235d39-c45d-5caf-a06e-0117a0a2941b

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
import Theorems.Thm_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ComponentChart_residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar
import Theorems.Thm_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_mem_integers_residue_ne_zero_of_qCoeff
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_ComponentChart_exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldC_one
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_eq_abv_evalAt_param_of_ord_residue_eq_one_of_forall_ord_eq_zero
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_sum_inv_jWidth_eq_of_ssJSet
import Theorems.Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge
import Theorems.Thm_ModularCurve_MultCovering_neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase"
p2m_attr_erase "instance" "instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"

set_option autoImplicit false

section W8CoreSlice
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 3200000

namespace P2MF2J

p2m_open "AlgebraicCurve ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates.ModularCurve Polynomial IsLocalRing"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.P2MF2J.ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "P2MF2J" "ord_nonneg_of_mem"
theorem ne_zero_of_ord_ne_zero (v : Place K F) {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem not_isUnit_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : ¬ IsUnit (⟨g, hg⟩ : v.toValuationSubring) := by
  rintro ⟨u, hu⟩
  have h0 := v.ord_coe_unit u
  rw [hu] at h0
  change v.ord g = 0 at h0
  omega

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
  (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (not_isUnit_of_ord_pos v hg h))

theorem mem_of_ord_pos (v : Place K F) {g : F} (h : 0 < v.ord g) : g ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (ne_zero_of_ord_ne_zero v h.ne') h.le

theorem ord_algebraMap' (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 :=
  (Place.hasValue_algebraMap v c).ord_eq_zero hc

namespace HasValue

private theorem _root_.P2MF2J.HasValue.add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

end HasValue
p2m_export "P2MF2J" "HasValue.add"

theorem hasValue_of_ord_sub_algebraMap_pos (v : Place K F) {g : F} {a : K}
    (h : 0 < v.ord (g - algebraMap K F a)) : v.HasValue g a := by
  have hm := mem_of_ord_pos v h
  have hI := mem_maximalIdeal_of_ord_pos v hm h
  have hgmem : g ∈ v.toValuationSubring := by
    have := add_mem hm (v.algebraMap_mem' a)
    rwa [sub_add_cancel] at this
  refine ⟨hgmem, ?_⟩
  have hsplit : (⟨g, hgmem⟩ : v.toValuationSubring)
      = ⟨g - algebraMap K F a, hm⟩ + ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := by
    apply Subtype.ext
    show g = (g - algebraMap K F a) + algebraMap K F a
    rw [sub_add_cancel]
  rw [hsplit, map_add, (residue_eq_zero_iff _).mpr hI, zero_add]
  exact (Place.hasValue_algebraMap v a).residue_eq

theorem evalAt_eq_of_hasValue {v : Place K F} (hv : v.IsRational) {g : F} {a : K} (h : v.HasValue g a) :
    v.evalAt g = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv h.mem]
  exact h.residue_eq

end PlaceFacts

section JLine

variable (k : Type*) [Field k] [DecidableEq k]

noncomputable abbrev jB : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

theorem ratFuncEquiv_algebraMap (Q : k[X]) :
    (ratFuncEquivCharLOneC k).toRingEquiv (algebraMap k[X] (RatFunc k) Q) = aeval (jB k) Q := by
  apply Subtype.ext
  change ((IntermediateField.equivOfEq (modularFunctionFieldC_one k).symm
      (RatFunc.algEquivOfTranscendental (jqModC k) _
        (algebraMap (Polynomial k) (RatFunc k) Q)) :
          ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = _
  have hcoe : ∀ (h : IntermediateField.adjoin k {jqModC k} = modularFunctionFieldC k 1)
      (x : ↥(IntermediateField.adjoin k {jqModC k})),
      ((IntermediateField.equivOfEq h x : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
        = (x : LaurentSeries k) := fun _ _ => rfl
  rw [hcoe, RatFunc.algEquivOfTranscendental_algebraMap]
  have e1 : (((aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q :
      ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k)) = aeval (jqModC k) Q := by
    rw [show (((aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q :
        ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k))
        = (IntermediateField.val _) (aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q) from rfl,
      ← Polynomial.aeval_algHom_apply]
    rfl
  have e2 : (((aeval (jB k) Q : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)) = aeval (jqModC k) Q := by
    rw [show (((aeval (jB k) Q : ↥(modularFunctionFieldC k 1)) : LaurentSeries k))
        = (IntermediateField.val _) (aeval (jB k) Q) from rfl, ← Polynomial.aeval_algHom_apply]
    rfl
  exact e1.trans e2.symm

theorem ord_charLGeomPlaceOfPoint_aeval (a : k) (Q : k[X]) (hQ : Q ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (aeval (jB k) Q) = Q.rootMultiplicity a := by
  have hplace : charLGeomPlaceOfPoint k a
      = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
          (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeOfPoint k a) := rfl
  rw [hplace, ← ratFuncEquiv_algebraMap, Place.ord_congrRingEquiv,
    RationalFunctionField.ord_placeOfPoint_algebraMap a hQ]

theorem aeval_jB_ne_zero (Q : k[X]) (hQ : Q ≠ 0) : aeval (jB k) Q ≠ 0 := by
  intro h
  apply hQ
  have h' : aeval (jqModC k) Q = 0 := by
    have := congrArg (IntermediateField.val (modularFunctionFieldC k 1)) h
    rw [← Polynomial.aeval_algHom_apply, map_zero] at this
    exact this
  exact (transcendental_iff.mp (transcendental_jqModC k)) Q h'

theorem hasValue_jB (a : k) : (charLGeomPlaceOfPoint k a).HasValue (jB k) a := by
  apply hasValue_of_ord_sub_algebraMap_pos
  have h := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a a
  rw [if_pos rfl] at h
  change (charLGeomPlaceOfPoint k a).ord (jB k - algebraMap k ↥(modularFunctionFieldC k 1) a) = 1 at h
  omega

theorem hasValue_aeval (a : k) (Q : k[X]) :
    (charLGeomPlaceOfPoint k a).HasValue (aeval (jB k) Q) (Q.eval a) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.aeval_add, eval_add]
    exact P2MF2J.HasValue.add hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    refine Place.HasValue.mul (Place.hasValue_algebraMap _ c) ?_
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact Place.hasValue_one _
    | succ n ih => rw [pow_succ, pow_succ]; exact Place.HasValue.mul ih (hasValue_jB k a)

theorem hasValue_aeval_mul_inv (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0) :
    (charLGeomPlaceOfPoint k a).HasValue (aeval (jB k) Q * (aeval (jB k) R)⁻¹) (Q.eval a * (R.eval a)⁻¹) :=
  Place.HasValue.mul (hasValue_aeval k a Q) ((hasValue_aeval k a R).inv hR)

theorem aeval_mul_inv_sub_algebraMap (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0) :
    aeval (jB k) Q * (aeval (jB k) R)⁻¹ - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹)
      = aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R)
          * (aeval (jB k) R * algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a))⁻¹ := by
  have hR' : aeval (jB k) R ≠ 0 := by
    intro h0
    have := (hasValue_aeval k a R).ne_zero hR
    exact this h0
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) ≠ 0 := (_root_.map_ne_zero _).mpr hR
  have e1 : aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R)
      = algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) * aeval (jB k) Q
        - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a) * aeval (jB k) R := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_C]
  have e2 : algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹)
      = algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a)
        * (algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a))⁻¹ := by
    rw [_root_.map_mul, map_inv₀]
  rw [e1, e2]
  field_simp

theorem ord_aeval_mul_inv_sub_value (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0)
    (hN : C (R.eval a) * Q - C (Q.eval a) * R ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord
        (aeval (jB k) Q * (aeval (jB k) R)⁻¹
          - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹))
      = (C (R.eval a) * Q - C (Q.eval a) * R).rootMultiplicity a := by
  have hR0 : R ≠ 0 := by rintro rfl; exact hR (eval_zero)
  have hR' : aeval (jB k) R ≠ 0 := aeval_jB_ne_zero k R hR0
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) ≠ 0 := (_root_.map_ne_zero _).mpr hR
  have hN' : aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R) ≠ 0 := aeval_jB_ne_zero k _ hN
  rw [aeval_mul_inv_sub_algebraMap k a Q R hR,
    (charLGeomPlaceOfPoint k a).ord_mul hN' (inv_ne_zero (mul_ne_zero hR' hc)),
    (charLGeomPlaceOfPoint k a).ord_inv, (charLGeomPlaceOfPoint k a).ord_mul hR' hc,
    ord_charLGeomPlaceOfPoint_aeval k a _ hN, ord_charLGeomPlaceOfPoint_aeval k a R hR0, ord_algebraMap' _ hR,
    Polynomial.rootMultiplicity_eq_zero (fun h : IsRoot R a => hR h)]
  simp

end JLine

end P2MF2J

end W8CoreSlice

section W8Step3bSlice
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

namespace P2MW8

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates.ModularCurve.MultCovering Polynomial"

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_evalAt (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValue f (v.evalAt f) :=
  ⟨hf, (v.algebraMap_evalAt hv hf).symm⟩

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 := by
  simpa using Place.hasValue_algebraMap v (0 : K)

theorem hasValue_const_smul {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (c : K) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]; exact (Place.hasValue_algebraMap v c).mul h

theorem hasValue_neg {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  have := hasValue_const_smul h (-1)
  simpa using this

theorem hasValue_sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  have := P2MF2J.HasValue.add h (hasValue_neg h')
  simpa [sub_eq_add_neg] using this

theorem hasValue_sum {v : Place K F} {ι : Type*} (s : Finset ι) (g : ι → F) (a : ι → K)
    (h : ∀ i ∈ s, v.HasValue (g i) (a i)) : v.HasValue (∑ i ∈ s, g i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero v
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact P2MF2J.HasValue.add (h b (Finset.mem_insert_self b s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ord_eq_zero_iff_value_ne_zero {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (hg : g ≠ 0) :
    v.ord g = 0 ↔ a ≠ 0 := by
  constructor
  · intro h0 ha
    subst ha
    rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, map_zero, sub_zero] at h
    rcases h.2 with h1 | h1
    · exact hg h1
    · omega
  · exact h.ord_eq_zero

theorem ord_sub_pos_of_hasValue {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (hne : g ≠ algebraMap K F a) :
    0 < v.ord (g - algebraMap K F a) := by
  rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos] at h
  rcases h.2 with h1 | h1
  · exact absurd h1 hne
  · exact h1

end Values

section JLineDeriv

variable (k : Type*) [Field k] [DecidableEq k]

def HasDerivVal (x : k) (g : ↥(modularFunctionFieldC k 1)) (a w : k) : Prop :=
  (charLGeomPlaceOfPoint k x).HasValue g a ∧
    (charLGeomPlaceOfPoint k x).HasValue
      ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k _ x)⁻¹) w

variable {k}

theorem jB_sub_ne_zero (x : k) : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x ≠ 0 := by
  intro h0
  have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k x x
  rw [if_pos rfl] at h1
  change (charLGeomPlaceOfPoint k x).ord (P2MF2J.jB k - algebraMap k _ x) = 1 at h1
  rw [h0, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem ord_jB_sub_self (x : k) :
    (charLGeomPlaceOfPoint k x).ord (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x) = 1 := by
  have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k x x
  rw [if_pos rfl] at h1
  exact h1

theorem HasDerivVal.add {x : k} {g g' : ↥(modularFunctionFieldC k 1)} {a w a' w' : k}
    (h : HasDerivVal k x g a w) (h' : HasDerivVal k x g' a' w') : HasDerivVal k x (g + g') (a + a') (w + w') := by
  refine ⟨P2MF2J.HasValue.add h.1 h'.1, ?_⟩
  have e : (g + g' - algebraMap k _ (a + a')) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
      = (g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
        + (g' - algebraMap k _ a') * (P2MF2J.jB k - algebraMap k _ x)⁻¹ := by
    rw [map_add]; ring
  rw [e]
  exact P2MF2J.HasValue.add h.2 h'.2

theorem HasDerivVal.smul {x : k} {g : ↥(modularFunctionFieldC k 1)} {a w : k}
    (h : HasDerivVal k x g a w) (c : k) : HasDerivVal k x (c • g) (c * a) (c * w) := by
  refine ⟨hasValue_const_smul h.1 c, ?_⟩
  have e : (c • g - algebraMap k _ (c * a)) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
      = c • ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k _ x)⁻¹) := by
    rw [map_mul, Algebra.smul_def, Algebra.smul_def]; ring
  rw [e]
  exact hasValue_const_smul h.2 c

theorem hasDerivVal_sum {x : k} {ι : Type*} (s : Finset ι) (g : ι → ↥(modularFunctionFieldC k 1)) (a w : ι → k)
    (h : ∀ i ∈ s, HasDerivVal k x (g i) (a i) (w i)) :
    HasDerivVal k x (∑ i ∈ s, g i) (∑ i ∈ s, a i) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨hasValue_zero _, ?_⟩
    rw [map_zero, sub_zero, zero_mul]; exact hasValue_zero _
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, Finset.sum_insert hb]
    exact (h b (Finset.mem_insert_self b s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasDerivVal.ord_sub_eq_one_iff {x : k} {g : ↥(modularFunctionFieldC k 1)} {a w : k}
    (h : HasDerivVal k x g a w) (hne : g ≠ algebraMap k _ a) :
    (charLGeomPlaceOfPoint k x).ord (g - algebraMap k _ a) = 1 ↔ w ≠ 0 := by
  have hu : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x ≠ 0 := jB_sub_ne_zero x
  have hga : g - algebraMap k _ a ≠ 0 := sub_ne_zero.mpr hne
  have hq : (g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹ ≠ 0 :=
    mul_ne_zero hga (inv_ne_zero hu)
  have key := ord_eq_zero_iff_value_ne_zero h.2 hq
  have e1 : g - algebraMap k _ a = ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹)
      * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x) := by
    rw [mul_assoc, inv_mul_cancel₀ hu, mul_one]
  have e2 : (charLGeomPlaceOfPoint k x).ord (g - algebraMap k _ a)
      = (charLGeomPlaceOfPoint k x).ord ((g - algebraMap k _ a) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹) + 1 := by
    conv_lhs => rw [e1]
    rw [(charLGeomPlaceOfPoint k x).ord_mul hq hu, ord_jB_sub_self x]
  rw [e2]
  constructor
  · intro h1
    exact key.mp (by omega)
  · intro hw
    rw [key.mpr hw]
    norm_num

theorem exists_hasDerivVal [IsAlgClosed k] (x : k) (g : ↥(modularFunctionFieldC k 1))
    (hg : g ∈ (charLGeomPlaceOfPoint k x).toValuationSubring) : ∃ a w : k, HasDerivVal k x g a w := by
  have hv : (charLGeomPlaceOfPoint k x).IsRational := ModularCurve.isRational_place_modularFunctionFieldC_one k _
  have h1 : (charLGeomPlaceOfPoint k x).HasValue g ((charLGeomPlaceOfPoint k x).evalAt g) := hasValue_evalAt _ hv hg
  have hu : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x ≠ 0 := jB_sub_ne_zero x

  have hmem : (g - algebraMap k _ ((charLGeomPlaceOfPoint k x).evalAt g)) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹
      ∈ (charLGeomPlaceOfPoint k x).toValuationSubring := by
    by_cases hga : g = algebraMap k _ ((charLGeomPlaceOfPoint k x).evalAt g)
    · rw [← hga, sub_self, zero_mul]; exact zero_mem _
    · have hpos := ord_sub_pos_of_hasValue h1 hga
      have hq : (g - algebraMap k _ ((charLGeomPlaceOfPoint k x).evalAt g)) * (P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x)⁻¹ ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr hga) (inv_ne_zero hu)
      apply (charLGeomPlaceOfPoint k x).mem_toValuationSubring_of_ord_nonneg_alt hq
      rw [(charLGeomPlaceOfPoint k x).ord_mul (sub_ne_zero.mpr hga) (inv_ne_zero hu), (charLGeomPlaceOfPoint k x).ord_inv, ord_jB_sub_self x]
      omega
  exact ⟨_, _, h1, hasValue_evalAt _ hv hmem⟩

theorem hasDerivVal_inv_jB_sub {x b : k} (hxb : x ≠ b) :
    HasDerivVal k x (P2MF2J.jB k - algebraMap k _ b)⁻¹ (x - b)⁻¹ (-((x - b) * (x - b))⁻¹) := by
  have hxb' : x - b ≠ 0 := sub_ne_zero.mpr hxb
  have hval : (charLGeomPlaceOfPoint k x).HasValue (P2MF2J.jB k - algebraMap k _ b) (x - b) := by
    have := hasValue_sub (P2MF2J.hasValue_jB k x) (Place.hasValue_algebraMap (charLGeomPlaceOfPoint k x) b)
    simpa using this
  have h1 : (charLGeomPlaceOfPoint k x).HasValue (P2MF2J.jB k - algebraMap k _ b)⁻¹ (x - b)⁻¹ := hval.inv hxb'
  refine ⟨h1, ?_⟩
  have hu : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) x ≠ 0 := jB_sub_ne_zero x
  have ht : P2MF2J.jB k - algebraMap k ↥(modularFunctionFieldC k 1) b ≠ 0 := hval.ne_zero hxb'
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (x - b) ≠ 0 := (_root_.map_ne_zero _).mpr hxb'
  have e2 : algebraMap k ↥(modularFunctionFieldC k 1) (x - b) - (P2MF2J.jB k - algebraMap k _ b)
      = -(P2MF2J.jB k - algebraMap k _ x) := by
    rw [map_sub]; ring
  have e1 : ((P2MF2J.jB k - algebraMap k _ b)⁻¹ - algebraMap k _ (x - b)⁻¹) * (P2MF2J.jB k - algebraMap k _ x)⁻¹
      = -((P2MF2J.jB k - algebraMap k _ b) * algebraMap k _ (x - b))⁻¹ := by
    rw [map_inv₀, inv_sub_inv ht hc, e2]
    field_simp
  rw [e1]
  have h2 : (charLGeomPlaceOfPoint k x).HasValue ((P2MF2J.jB k - algebraMap k _ b) * algebraMap k _ (x - b)) ((x - b) * (x - b)) :=
    hval.mul (Place.hasValue_algebraMap _ _)
  exact hasValue_neg (h2.inv (mul_ne_zero hxb' hxb'))

end JLineDeriv

end P2MW8

end W8Step3bSlice

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldC_one ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty ord_charLGeomPlaceEquiv_placeInfty_jqModC MultCovering.mem_zeroChart_nodes_iff deg_eq_one_modularFunctionFieldBar MultCovering.zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes isCurveOver_modularFunctionFieldC_of_perfectField sum_inv_jWidth_eq_of_ssJSet MultCovering.mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge MultCovering.neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "hasseExp goodFamilyZero FamCtx mAnnuli Fbar ChartCtx zeroChart chart ssValue ssValue_injective exists_ssValue_eq nodeSrc AnnCtx mem_zeroChart_nodes_iff zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero"
p2m_open "ModularCurve.MultCovering ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg"

open AlgebraicCurve IsLocalRing

section GenericHelpers

theorem evalAt_mul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_algebraMap_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

theorem chart_isUnit_of_residue_ne_zero_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

theorem vs_inv_mem_of_isUnit_D {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

theorem chart_residue_inv_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

theorem ord_eq_zero_of_evalAt_ne_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h' | h'
    · simp [h']
    · exact h'
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem abv_lt_one_of_mem_maximalIdeal_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {m : ↥A} (hm : m ∈ IsLocalRing.maximalIdeal ↥A) : μ (m : AlgebraicClosure ℚ) < 1 := by
  have hle : μ (m : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 m.2
  refine lt_of_le_of_ne hle fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have hm0 : (m : AlgebraicClosure ℚ) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hinv : (m : AlgebraicClosure ℚ)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0)⟩

theorem isRational_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (h : v.deg = 1) :
    v.IsRational := by
  intro x
  have h1 : Module.finrank K v.ResidueField = 1 := h
  have htop : (⊥ : Subalgebra K v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by rw [htop]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hx

theorem isRational_modularFunctionFieldBar {p : ℕ} [Fact p.Prime] (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) :
    v.IsRational :=
  isRational_of_deg_eq_one v (ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * p) v)

theorem minor_mulVec_D {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end GenericHelpers

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldC_one ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty ord_charLGeomPlaceEquiv_placeInfty_jqModC MultCovering.mem_zeroChart_nodes_iff deg_eq_one_modularFunctionFieldBar MultCovering.zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes isCurveOver_modularFunctionFieldC_of_perfectField sum_inv_jWidth_eq_of_ssJSet MultCovering.mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge MultCovering.neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "hasseExp goodFamilyZero FamCtx mAnnuli Fbar ChartCtx zeroChart chart ssValue ssValue_injective exists_ssValue_eq nodeSrc AnnCtx mem_zeroChart_nodes_iff zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero"
namespace G0Aux
p2m_open "ModularCurve.MultCovering ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg"

open AlgebraicCurve IsLocalRing

theorem evalAt_sub_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem exists_eq_algebraMap_of_forall_ord_nonneg {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    [IsCurveOver k F] (v₀ : Place k F) (f : F) (hreg : ∀ v : Place k F, 0 ≤ v.ord f) :
    ∃ c : k, f = algebraMap k F c := by
  classical
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, map_zero]⟩
  haveI hPD : HasPrincipalDivisors k F := IsCurveOver.hasPrincipalDivisors
  have hrat : ∀ v : Place k F, v.IsRational := fun v =>
    isRational_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  have hfv : f ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hf0 (hreg v₀)
  set c : k := v₀.evalAt f with hc
  refine ⟨c, ?_⟩
  by_contra hne
  set g : F := f - algebraMap k F c with hg
  have hg0 : g ≠ 0 := sub_ne_zero.mpr hne

  have hgreg : ∀ v : Place k F, 0 ≤ v.ord g := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hf0 (hreg v)) (v.algebraMap_mem' c))

  have hgv : g ∈ v₀.toValuationSubring := sub_mem hfv (v₀.algebraMap_mem' c)
  have hev : v₀.evalAt g = 0 := by
    rw [hg, evalAt_sub_D v₀ (hrat v₀) hfv (v₀.algebraMap_mem' c), evalAt_algebraMap_D, hc, sub_self]
  have hpos : 0 < v₀.ord g := by
    refine lt_of_le_of_ne (hgreg v₀) fun h0 => ?_

    have hres0 : IsLocalRing.residue v₀.toValuationSubring ⟨g, hgv⟩ = 0 := by
      rw [← v₀.algebraMap_evalAt (hrat v₀) hgv, hev, map_zero]

    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v₀.toValuationSubring
    obtain ⟨u, hu⟩ := v₀.exists_unit_mul_zpow hg0 hπ
    rw [← h0, zpow_zero, mul_one] at hu
    have hgu : (⟨g, hgv⟩ : v₀.toValuationSubring) = (u : v₀.toValuationSubring) := Subtype.ext hu
    rw [hgu] at hres0
    exact (u.isUnit.map (IsLocalRing.residue v₀.toValuationSubring)).ne_zero hres0

  obtain ⟨D, hD, hdeg⟩ := hPD.exists_divisor g hg0
  have hall : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hgreg v
  have hv₀ : 0 < D v₀ := by rw [hD v₀]; exact hpos
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hv₀.ne'
  have hdegsum : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
    conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v (D v)
  have hdegpos : 0 < Divisor.degree D := by
    rw [hdegsum]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) := by
          rw [IsCurveOver.deg_eq_one_of_isAlgClosed v₀, Nat.cast_one, mul_one]; exact hv₀
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum (fun v _ => mul_nonneg (hall v) (Int.natCast_nonneg _)) hmem
  rw [hdeg] at hdegpos
  exact lt_irrefl 0 hdegpos

end ModularCurve.MultCovering.G0Aux

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~exists_eq_algebraMap_of_forall_ord_nonneg P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates.ModularCurve.MultCovering"

open P2MW8 P2MF2J ModularCurve.MultCovering.G0Aux in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (he : jWidth (ssValue Γ e) ≠ 1) :
    (∃ l : Fin r, hasseExp Φ.toFamData l = 1 ∧ ∃ c : ResidueField ↥A,
        (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩
          - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c) = 1) ∧
    (∀ e' : Fin (mAnnuli p), e' ≠ e → jWidth (ssValue Γ e') ≠ 1 →
      ∃ l : Fin r, hasseExp Φ.toFamData l = 1 ∧
        (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)
          ≠ (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by omega
  haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField _ 1
  have hrat : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v.IsRational :=
    fun v => ModularCurve.isRational_place_modularFunctionFieldC_one _ v
  have hfinj : Function.Injective (fun x : ResidueField ↥A => x ^ p) := by
    intro x y hxy
    exact frobenius_inj (ResidueField ↥A) p (by simpa [frobenius_def] using hxy)
  have hnodeSrc : ∀ e' : Fin (mAnnuli p), nodeSrc Γ e' = charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e' ^ p) :=
    fun e' => rfl

  have h1728ne : (1728 : ResidueField ↥A) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 1728 := (CharP.cast_eq_zero_iff (ResidueField ↥A) p 1728).mp (by exact_mod_cast h0)
    have h2 : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num at hdvd ⊢; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  have hexb : ∃ eb : Fin (mAnnuli p), jWidth (ssValue Γ eb) = 1 := by
    by_contra hnone
    push_neg at hnone
    have hsub : Γ.hfin.toFinset ⊆ ({0, 1728} : Finset (ResidueField ↥A)) := by
      intro a ha
      obtain ⟨e', he'⟩ := exists_ssValue_eq Γ a (Γ.hfin.mem_toFinset.mp ha)
      rw [Finset.mem_insert, Finset.mem_singleton, ← he']
      by_contra h; push_neg at h
      exact hnone e' (jWidth_of_ne h.1 h.2)
    have hsum := ModularCurve.sum_inv_jWidth_eq_of_ssJSet p hp5 (ResidueField ↥A) Γ.hfin.toFinset
      (fun j => Set.Finite.mem_toFinset Γ.hfin)
    have hle : ∑ j ∈ Γ.hfin.toFinset, ((jWidth j : ℚ))⁻¹ ≤ ∑ j ∈ ({0, 1728} : Finset (ResidueField ↥A)), ((jWidth j : ℚ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    rw [Finset.sum_pair h1728ne.symm, jWidth_of_eq_zero rfl, jWidth_of_eq_1728 rfl h1728ne] at hle
    have hge : (1 : ℚ) ≤ ((p : ℚ) - 1) / 12 := by
      have : (13 : ℚ) ≤ p := by exact_mod_cast hp13
      linarith
    rw [← hsum] at hge
    push_cast at hle
    linarith
  obtain ⟨eb, hwb⟩ := hexb
  have hbe : eb ≠ e := by intro h; rw [h] at hwb; exact he hwb

  set β : ResidueField ↥A := ssValue Γ eb ^ p with hβ
  set f : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := (jB (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ β)⁻¹ with hf
  have hjsub := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (ResidueField ↥A)
  have hjβ0 : jB (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ β ≠ 0 := by
    intro h0; have := hjsub β β; rw [if_pos rfl] at this
    change (charLGeomPlaceOfPoint _ β).ord (jB (ResidueField ↥A) - algebraMap _ _ β) = 1 at this
    rw [h0, Place.ord_zero] at this; exact zero_ne_one this
  have hf0 : f ≠ 0 := inv_ne_zero hjβ0

  have hordf_pt : ∀ c : ResidueField ↥A, (charLGeomPlaceOfPoint (ResidueField ↥A) c).ord f = -(if β = c then 1 else 0) := by
    intro c
    rw [hf, Place.ord_inv]
    congr 1
    exact hjsub c β
  have hnodeb : nodeSrc Γ eb ∈ (zeroChart Γ).nodes := (Δ.attached_src eb).1
  have hreg : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord f := by
    intro v hv
    rcases ModularCurve.eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (ResidueField ↥A) v with ⟨c, rfl⟩ | hinf
    · rw [hordf_pt c]
      split_ifs with hc
      · exfalso; apply hv; rw [← hc, ← hnodeSrc eb]; exact hnodeb
      · simp
    ·
      rw [hinf, hf, Place.ord_inv]
      have hj : (charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A))).ord
          (jB (ResidueField ↥A)) = -1 := ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (ResidueField ↥A)
      have hjB0 : jB (ResidueField ↥A) ≠ 0 := by
        intro h0; rw [h0, Place.ord_zero] at hj; norm_num at hj
      by_cases hβ0 : β = 0
      · rw [hβ0, map_zero, sub_zero, hj]; norm_num
      · have hc0 : algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) β ≠ 0 := (map_ne_zero _).mpr hβ0
        have hc : (charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A))).ord
            (-(algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) β)) = 0 := by
          rw [← map_neg]; exact AlgebraicCurve.Place.ord_algebraMap _ _
        rw [sub_eq_add_neg, AlgebraicCurve.Place.ord_add_eq_of_lt _ hjB0 (neg_ne_zero.mpr hc0) (by rw [hj, hc]; norm_num), hj]
        norm_num
  have hnode : ∀ e' : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e') : ℕ) : ℤ) ≤ (nodeSrc Γ e').ord f := by
    intro e'
    rw [hnodeSrc, hordf_pt]
    by_cases h' : e' = eb
    · subst h'
      rw [if_pos rfl, hwb]; norm_num
    · have hne : β ≠ ssValue Γ e' ^ p := fun h0 => h' (ssValue_injective Γ (hfinj h0)).symm
      rw [if_neg hne, neg_zero]
      exact neg_nonpos.mpr (Int.natCast_nonneg _)
  have hspan := ModularCurve.MultCovering.mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge
    p hp5 A hA Γ Δ Φ hint hLI f hreg hnode
  rw [Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨cf, hcf⟩ := hspan

  obtain ⟨hintF, hF1⟩ := ModularCurve.MultCovering.neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero p A hA Γ Δ Φ
  obtain ⟨hintZ, hZ3⟩ := ModularCurve.MultCovering.zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p A hA Γ Φ
  have hu_eq : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hintF l⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ :=
    fun l => by congr 1
  have hu_eq' : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ :=
    fun l => by congr 1

  have hregwide : ∀ (e' : Fin (mAnnuli p)), jWidth (ssValue Γ e') ≠ 1 → ∀ l : Fin r, hasseExp Φ.toFamData l ≤ 1 →
      0 ≤ (nodeSrc Γ e').ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
    intro e' hw l hl
    have h1 := hF1 e' l
    rw [hu_eq] at h1
    have hw2 : 2 ≤ jWidth (ssValue Γ e') := by
      have : 1 ≤ jWidth (ssValue Γ e') := by unfold jWidth; split_ifs <;> norm_num
      omega
    have hdiv : hasseExp Φ.toFamData l / jWidth (ssValue Γ e') = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv] at h1; simpa using h1

  have hconst : ∀ l : Fin r, hasseExp Φ.toFamData l = 0 → ∃ c : ResidueField ↥A,
      (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ = algebraMap _ _ c := by
    intro l hl
    apply exists_eq_algebraMap_of_forall_ord_nonneg (nodeSrc Γ e)
    intro v
    by_cases hv : v ∈ (zeroChart Γ).nodes
    · obtain ⟨a, ha, rfl⟩ := (ModularCurve.MultCovering.mem_zeroChart_nodes_iff Γ v).mp hv
      obtain ⟨e', he'⟩ := exists_ssValue_eq Γ a ha
      rw [← he', ← hnodeSrc]
      have h1 := hF1 e' l
      rw [hu_eq, hl, Nat.zero_div] at h1; simpa using h1
    · have := hZ3 l v hv; rwa [hu_eq'] at this

  have hαβ : ∀ e' : Fin (mAnnuli p), e' ≠ eb → ssValue Γ e' ^ p ≠ β :=
    fun e' h' h0 => h' (ssValue_injective Γ (hfinj h0))
  have hfD : ∀ e' : Fin (mAnnuli p), e' ≠ eb →
      HasDerivVal (ResidueField ↥A) (ssValue Γ e' ^ p) f (ssValue Γ e' ^ p - β)⁻¹
        (-((ssValue Γ e' ^ p - β) * (ssValue Γ e' ^ p - β))⁻¹) :=
    fun e' h' => hasDerivVal_inv_jB_sub (hαβ e' h')
  have hfval : ∀ e' : Fin (mAnnuli p), e' ≠ eb → (nodeSrc Γ e').evalAt f = (ssValue Γ e' ^ p - β)⁻¹ :=
    fun e' h' => by rw [hnodeSrc]; exact evalAt_eq_of_hasValue (hrat _) (hfD e' h').1

  refine ⟨?_, fun e' hne' hw' => ?_⟩
  swap
  · by_contra hall
    push_neg at hall

    have heq : ∀ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1},
        (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩)
          = (nodeSrc Γ e').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩) := by
      intro i
      rcases Nat.lt_or_ge (hasseExp Φ.toFamData i) 1 with h0 | h1
      · obtain ⟨c, hc⟩ := hconst i (by omega)
        rw [hc, evalAt_eq_of_hasValue (hrat _) (Place.hasValue_algebraMap _ c),
          evalAt_eq_of_hasValue (hrat _) (Place.hasValue_algebraMap _ c)]
      · exact hall i (le_antisymm i.2 h1)

    have hvals : ∀ (e'' : Fin (mAnnuli p)), jWidth (ssValue Γ e'') ≠ 1 →
        (nodeSrc Γ e'').evalAt f = ∑ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1},
          cf i * (nodeSrc Γ e'').evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩) := by
      intro e'' hw''
      rw [← hcf]
      apply evalAt_eq_of_hasValue (hrat _)
      apply hasValue_sum
      intro i _
      apply hasValue_const_smul
      exact hasValue_evalAt _ (hrat _) ((nodeSrc Γ e'').mem_of_ord_nonneg
        (hLI.ne_zero i.1) (hregwide e'' hw'' i i.2))
    have hfeq : (nodeSrc Γ e).evalAt f = (nodeSrc Γ e').evalAt f := by
      rw [hvals e he, hvals e' hw']
      exact Finset.sum_congr rfl fun i _ => by rw [heq i]
    rw [hfval e hbe.symm, hfval e' (fun h => hw' (h ▸ hwb)), inv_inj, sub_left_inj] at hfeq
    exact hne' (ssValue_injective Γ (hfinj hfeq)).symm

  · by_contra hall
    push_neg at hall

    set x : ResidueField ↥A := ssValue Γ e ^ p with hx
    have hmem : ∀ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1},
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩ ∈ (charLGeomPlaceOfPoint (ResidueField ↥A) x).toValuationSubring := by
      intro i
      rw [← hnodeSrc]
      exact (nodeSrc Γ e).mem_of_ord_nonneg (hLI.ne_zero i.1) (hregwide e he i i.2)
    have hD : ∀ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1}, ∃ a w : ResidueField ↥A,
        HasDerivVal (ResidueField ↥A) x ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩) a w ∧ w = 0 := by
      intro i
      obtain ⟨a, w, haw⟩ := exists_hasDerivVal x _ (hmem i)
      refine ⟨a, w, haw, ?_⟩

      rcases Nat.lt_or_ge (hasseExp Φ.toFamData i) 1 with h0 | h1
      · obtain ⟨c, hc⟩ := hconst i (by omega)

        have hcD : HasDerivVal (ResidueField ↥A) x ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩) c 0 := by
          rw [hc]
          refine ⟨Place.hasValue_algebraMap _ c, ?_⟩
          rw [sub_self, zero_mul]
          exact hasValue_zero _
        have ha : a = c := by
          rw [← evalAt_eq_of_hasValue (hrat _) haw.1, ← evalAt_eq_of_hasValue (hrat _) hcD.1]
        subst ha
        rw [← evalAt_eq_of_hasValue (hrat _) haw.2, ← evalAt_eq_of_hasValue (hrat _) hcD.2]
      · have hn1 : hasseExp Φ.toFamData i = 1 := le_antisymm i.2 h1
        by_contra hw0
        by_cases hga : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩ = algebraMap _ _ a
        ·
          apply hw0
          have h2 := haw.2
          rw [hga, sub_self, zero_mul] at h2
          rw [← evalAt_eq_of_hasValue (hrat _) h2, ← evalAt_eq_of_hasValue (hrat _) (hasValue_zero _)]
        · have h1' := (haw.ord_sub_eq_one_iff hga).mpr hw0
          rw [← hnodeSrc] at h1'
          exact hall i hn1 a h1'
    choose a w haw hw0 using hD

    have hfD' : HasDerivVal (ResidueField ↥A) x f (∑ i, cf i * a i) (∑ i, cf i * w i) := by
      rw [← hcf]
      exact hasDerivVal_sum Finset.univ _ _ _ fun i _ => (haw i).smul (cf i)
    have hw00 : ∑ i, cf i * w i = 0 := Finset.sum_eq_zero fun i _ => by rw [hw0 i, mul_zero]
    rw [hw00] at hfD'
    have hfD0 := hfD e hbe.symm

    have hvaleq : (∑ i, cf i * a i) = (x - β)⁻¹ := by
      rw [← evalAt_eq_of_hasValue (hrat _) hfD'.1, ← evalAt_eq_of_hasValue (hrat _) hfD0.1]
    have hq1 := hfD'.2
    have hq2 := hfD0.2
    rw [hvaleq] at hq1
    have : (0 : ResidueField ↥A) = -((x - β) * (x - β))⁻¹ := by
      rw [← evalAt_eq_of_hasValue (hrat _) hq1, ← evalAt_eq_of_hasValue (hrat _) hq2]
    have hxβ : x - β ≠ 0 := sub_ne_zero.mpr (hαβ e hbe.symm)
    exact absurd this.symm (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero hxβ hxβ)))

end S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_hasseExp_eq_one_unramified_and_separates (solution)
