-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7a526ce4-c0a0-59b0-a4bf-05d8dcd1b8c5

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
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
import Theorems.Thm_ModularCurve_MultCovering_exists_combination_hasseExp_two_eq_prod_widthOne
import Theorems.Thm_ModularCurve_MultCovering_mem_infChart_integers_of_forall_coeff_mem
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_MultCovering_coeffMap_frobenius_zeroChart_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 3200000

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange ssJSet PlaceSpecialization.LevelOneProlongationPair jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldC_one PlaceSpecialization ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar coeffMap_jqModC jWidth jWidth_of_eq_zero jWidth_of_ne jWidth_map coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem ssJSet_nonempty ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty pow_mem_ssJSet_iff_of_perfectField zero_mem_ssJSet_iff ofNat1728_mem_ssJSet_iff ord_charLGeomPlaceEquiv_placeInfty_jqModC pow_q_sq_eq_self_of_mem_ssJSet MultCovering.coeffMap_frobenius_zeroChart_residue_goodFamilyZero"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "FamData zeroSeries coe_frickeInvolutionBar_t hasseContent hasseExp goodFamilyZero ssPolyBar FamCtx jBar mAnnuli ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq nodeSrc nodeTgt AnnCtx cuspZeroBar_not_mem_infChart_dom mem_zeroChart_nodes_iff hasseExp_le_two_of_thirteen_le exists_combination_hasseExp_two_eq_prod_widthOne mem_infChart_integers_of_forall_coeff_mem coeffMap_frobenius_zeroChart_residue_goodFamilyZero mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge"
namespace P2Mhsep
p2m_open "ModularCurve.MultCovering~hasseContent_nonneg ModularCurve~jBar"
namespace P2MF2J

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero.ModularCurve Polynomial IsLocalRing"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem HasValue.add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

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

set_option Elab.async false

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero.ModularCurve IsLocalRing"

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

def IsContent (Φ : FamData p r) (l : Fin r) (n : ℤ) : Prop :=
  (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
    (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n)

theorem isContent_hasseContent (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n) :
    IsContent Φ l (hasseContent Φ l) := by
  have hex' : ∃ n : ℤ, (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
      (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n) := hex
  rw [hasseContent, dif_pos hex']
  exact hex'.choose_spec

theorem IsContent.eq {Φ : FamData p r} {l : Fin r} {m n : ℤ} (hm : IsContent Φ l m) (hn : IsContent Φ l n) :
    m = n := by
  obtain ⟨k, hk, hkm⟩ := hm.2
  obtain ⟨k', hk', hkn⟩ := hn.2
  have h1 := hn.1 k hk
  have h2 := hm.1 k' hk'
  rw [hkm] at h1; rw [hkn] at h2
  exact le_antisymm h2 h1

theorem hasseContent_eq_of_isContent {Φ : FamData p r} {l : Fin r} {n : ℤ} (hn : IsContent Φ l n) :
    hasseContent Φ l = n :=
  (isContent_hasseContent Φ l ⟨n, hn⟩).eq hn

theorem zeroSeries_ne_zero (Φ : FamData p r) (l : Fin r) (ht0 : Φ.t l ≠ 0) : zeroSeries Φ l ≠ 0 := by
  intro h
  apply ht0
  have h1 : ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
    rw [coe_frickeInvolutionBar_t, h, map_zero]
  have h2 : frickeInvolutionBar (1 * p) (Φ.t l) = 0 := Subtype.ext h1
  exact (EmbeddingLike.map_eq_zero_iff (f := frickeInvolutionBar (1 * p))).mp h2

theorem exists_isContent (Φ : FamData p r) (l : Fin r) (ht0 : Φ.t l ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (hcA : ∀ k : ℤ, c * ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) :
    ∃ n : ℤ, IsContent Φ l n := by
  have hcA' : ∀ k : ℤ, c * (coeffEmb (AlgebraicClosure ℚ) (zeroSeries Φ l)).coeff k ∈ A := by
    intro k; rw [← coe_frickeInvolutionBar_t]; exact hcA k
  obtain ⟨n, h1, k₀, hk₀, hk₀n⟩ := exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
    (Fact.out : p.Prime) A hA (zeroSeries Φ l) (zeroSeries_ne_zero Φ l ht0) c hc hcA'
  exact ⟨n, h1, k₀, hk₀, hk₀n⟩

theorem zeroSeries_rescaled_gaussUnit (Φ : FamData p r) (l : Fin r) {n : ℤ} (hn : IsContent Φ l n)
    {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K) (hA : A.LiesOverPrime p) :
    (∀ k : ℤ, (coeffEmb K (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k ∈ A) ∧
      ∃ k : ℤ, (coeffEmb K (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k ∉ A.nonunits := by
  obtain ⟨k₀, hk₀, hk₀n⟩ := hn.2
  obtain ⟨h1, h2⟩ := coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat A (Fact.out : p.Prime)
    hA (zeroSeries Φ l) n hn.1 k₀ hk₀ hk₀n
  exact ⟨h1, k₀, h2⟩

theorem hasseExp_cast (Φ : FamData p r) (l : Fin r) (h0 : 0 ≤ hasseContent Φ l) :
    (hasseExp Φ l : ℤ) = hasseContent Φ l := by
  rw [hasseExp, Int.toNat_of_nonneg h0]

theorem coe_frickeInvolutionBar_goodFamilyZero (Φ : FamData p r) (l : Fin r) :
    ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l) := by
  rw [goodFamilyZero, map_mul, map_inv₀, AlgEquiv.commutes]

  have hcoe : (((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ * frickeInvolutionBar (1 * p) (Φ.t l) :
          modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ *
        ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
          LaurentSeries (AlgebraicClosure ℚ)) := by
    push_cast
    rfl
  rw [hcoe, coe_frickeInvolutionBar_t]
  ext k
  rw [coeffEmb_coeff, ← map_inv₀, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul,
    HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul]
  show ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l)⁻¹ * algebraMap ℚ (AlgebraicClosure ℚ) ((zeroSeries Φ l).coeff k)
    = algebraMap ℚ (AlgebraicClosure ℚ) ((((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l).coeff k)
  rw [show ((((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l).coeff k)
      = ((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ * (zeroSeries Φ l).coeff k from rfl,
    map_mul, map_inv₀, zpow_natCast, map_pow, map_natCast]

theorem frickeInvolutionBar_goodFamilyZero_qCoeff (Φ : FamData p r) (l : Fin r)
    (hex : ∃ n : ℤ, IsContent Φ l n) (h0 : 0 ≤ hasseContent Φ l)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ hf : ∀ k : ℤ, ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A,
      ∃ k : ℤ, IsUnit (⟨_, hf k⟩ : ↥A) := by
  have hn := isContent_hasseContent Φ l hex
  obtain ⟨h1, k₀, h2⟩ := zeroSeries_rescaled_gaussUnit Φ l hn A hA
  rw [← hasseExp_cast Φ l h0] at h1 h2
  refine ⟨fun k => ?_, k₀, ?_⟩
  · rw [coe_frickeInvolutionBar_goodFamilyZero]; exact h1 k
  · rw [ValuationSubring.valuation_eq_one_iff]
    have hx : ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k₀
        = (coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l)).coeff k₀ := by
      rw [coe_frickeInvolutionBar_goodFamilyZero]
    have h3 : ¬ A.valuation ((coeffEmb (AlgebraicClosure ℚ)
        (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l)).coeff k₀) < 1 :=
      fun h => h2 ((ValuationSubring.mem_nonunits_iff A).mpr h)
    refine le_antisymm (A.valuation_le_one _) ?_
    rw [not_lt, ← hx] at h3
    exact h3

section Sign

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (C : ComponentChart A (modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (ResidueField ↥A) 1))
  (hint_iff : ∀ g : modularFunctionFieldBar (1 * p), g ∈ C.integers ↔
    (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
  (hres : ∀ (g : modularFunctionFieldBar (1 * p))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
    ∃ h : g ∈ C.integers,
      ((C.residue ⟨g, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
        = CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hg⟩)
  (hnodes : ∀ x, x ∈ C.nodes ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x)
  (hzero_not : cuspZeroBar (1 * p) ∉ C.dom)

  (hcrit : ∀ (g : modularFunctionFieldBar (1 * p))
    (hf : ∀ k : ℤ, (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A)
    (hu : ∃ k : ℤ, IsUnit (⟨(g : LaurentSeries (AlgebraicClosure ℚ)).coeff k, hf k⟩ : ↥A)),
      ∃ h : g ∈ C.integers, C.residue ⟨g, h⟩ ≠ 0)

theorem coe_frickeInvolutionBar_algebraMap_mul (Φ : FamData p r) (l : Fin r) (y : ℚ) :
    ((frickeInvolutionBar (1 * p)
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) y) * Φ.t l) :
          modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (y • zeroSeries Φ l) := by
  rw [map_mul, AlgEquiv.commutes]
  push_cast
  rw [coe_frickeInvolutionBar_t]
  ext k
  rw [coeffEmb_coeff]
  first
  | rw [IntermediateField.algebraMap_apply]
  | skip
  rw [algebraMap_laurentSeries_eq_single,
    HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul,
    show ((y • zeroSeries Φ l).coeff k) = y * (zeroSeries Φ l).coeff k from rfl, map_mul]

include hA hcrit in

theorem exists_frickeInvolutionBar_smul_mem_integers (Φ : FamData p r) (l : Fin r) {n : ℤ} (hn : IsContent Φ l n) :
    ∃ h : frickeInvolutionBar (1 * p)
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹)) * Φ.t l) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨h1, k₀, h2⟩ := zeroSeries_rescaled_gaussUnit Φ l hn A hA
  have hf : ∀ k : ℤ, ((frickeInvolutionBar (1 * p)
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹)) * Φ.t l) : modularFunctionFieldBar (1 * p)) :
          LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by
    intro k; rw [coe_frickeInvolutionBar_algebraMap_mul]; exact h1 k
  refine hcrit _ hf ⟨k₀, ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff]
  refine le_antisymm (A.valuation_le_one _) ?_
  have h3 : ¬ A.valuation ((coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k₀) < 1 :=
    fun h => h2 ((ValuationSubring.mem_nonunits_iff A).mpr h)
  rw [not_lt, ← coe_frickeInvolutionBar_algebraMap_mul] at h3
  exact h3

include hA hint_iff hres hnodes hzero_not hcrit in

theorem hasseContent_nonneg_of_chart (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n)
    (ht0 : Φ.t l ≠ 0) (ht_int : Φ.t l ∈ C.integers)
    (htpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p)) :
    0 ≤ hasseContent Φ l := by
  by_contra hneg
  push_neg at hneg
  have hnI := isContent_hasseContent Φ l hex
  set n := hasseContent Φ l with hn

  set m : ℕ := (-n).toNat with hm_def
  have hm : (m : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm; omega
  have hy : algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹) = (p : AlgebraicClosure ℚ) ^ m := by
    rw [map_inv₀, map_zpow₀, map_natCast, ← zpow_neg, ← hm, zpow_natCast]
  have key := exists_frickeInvolutionBar_smul_mem_integers A hA C hcrit Φ l hnI
  rw [hy] at key
  obtain ⟨hwf_int, hwf_res⟩ := key

  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hxA : (p : AlgebraicClosure ℚ) ^ m ∈ A := pow_mem hpA m
  have hx_int : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) ∈ C.integers :=
    (C.algebraMap_mem_iff _).mpr hxA
  have hf_int : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) * Φ.t l ∈ C.integers :=
    mul_mem hx_int ht_int
  have hres_p : IsLocalRing.residue ↥A ⟨(p : AlgebraicClosure ℚ) ^ m, hxA⟩ = 0 := by
    have h1 : (⟨(p : AlgebraicClosure ℚ) ^ m, hxA⟩ : ↥A) = (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ^ m := by
      apply Subtype.ext; simp
    rw [h1, map_pow, (IsLocalRing.residue_eq_zero_iff _).mpr, zero_pow hm0]
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
  have hresf : C.residue ⟨_, hf_int⟩ = 0 := by
    have h1 : (⟨_, hf_int⟩ : C.integers) = ⟨_, hx_int⟩ * ⟨Φ.t l, ht_int⟩ := rfl
    rw [h1, map_mul, C.residue_algebraMap ⟨_, hxA⟩, hres_p, map_zero, zero_mul]
  obtain ⟨a, ha⟩ := ssJSet_nonempty (q := p) (k := ResidueField ↥A)
  have hval : (charLGeomPlaceOfPoint (ResidueField ↥A) a).HasValue (C.residue ⟨_, hf_int⟩) 0 := by
    rw [hresf]; simpa using (charLGeomPlaceOfPoint (ResidueField ↥A) a).hasValue_algebraMap
      (F := ↥(modularFunctionFieldC (ResidueField ↥A) 1)) 0
  have hx0 : (p : AlgebraicClosure ℚ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hf0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) * Φ.t l ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).mpr hx0) ht0
  have hfpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      W.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) * Φ.t l) < 0 →
        W = cuspInftyBar (1 * p) := by
    intro W hW
    apply htpole W
    rwa [W.ord_mul ((map_ne_zero _).mpr hx0) ht0, Place.ord_algebraMap, zero_add] at hW
  exact hwf_res (ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar A hA C hint_iff hres hnodes hzero_not _ hf0 hfpole hf_int hwf_int a ha hval)

include hA hint_iff hres hnodes hzero_not hcrit in

theorem one_le_hasseExp_of_chart (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n)
    (ht0 : Φ.t l ≠ 0) (ht_int : Φ.t l ∈ C.integers)
    (htpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p))
    (hnode : ∃ a ∈ ssJSet p (ResidueField ↥A), (charLGeomPlaceOfPoint (ResidueField ↥A) a).HasValue (C.residue ⟨Φ.t l, ht_int⟩) 0) :
    1 ≤ hasseExp Φ l := by
  have h0 := hasseContent_nonneg_of_chart A hA C hint_iff hres hnodes hzero_not hcrit Φ l hex ht0 ht_int htpole
  by_contra hlt
  push_neg at hlt
  have hE : hasseExp Φ l = 0 := by omega
  have hc0 : hasseContent Φ l = 0 := by
    have := hasseExp_cast Φ l h0; rw [hE] at this; exact_mod_cast this.symm
  have hnI := isContent_hasseContent Φ l hex
  rw [hc0] at hnI
  have key := exists_frickeInvolutionBar_smul_mem_integers A hA C hcrit Φ l hnI
  have h1 : algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ (0 : ℤ))⁻¹) = 1 := by simp
  rw [h1, map_one, one_mul (Φ.t l)] at key
  obtain ⟨hwf_int, hwf_res⟩ := key
  obtain ⟨a, ha, hval⟩ := hnode
  exact hwf_res (ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar A hA C hint_iff hres hnodes hzero_not _ ht0 htpole ht_int hwf_int a ha hval)

include hA hint_iff hres hnodes hzero_not hcrit in

theorem goodFamilyZero_mem_comap_integers_residue_ne_zero_of_chart (Φ : FamData p r) (l : Fin r)
    (hex : ∃ n : ℤ, IsContent Φ l n) (ht0 : Φ.t l ≠ 0) (ht_int : Φ.t l ∈ C.integers)
    (htpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p)) :
    ∃ h : goodFamilyZero Φ l ∈ (C.comap (frickeInvolutionBar (1 * p))).integers,
      (C.comap (frickeInvolutionBar (1 * p))).residue ⟨_, h⟩ ≠ 0 := by
  have h0 := hasseContent_nonneg_of_chart A hA C hint_iff hres hnodes hzero_not hcrit Φ l hex ht0 ht_int htpole
  obtain ⟨hf, k, hu⟩ := frickeInvolutionBar_goodFamilyZero_qCoeff Φ l hex h0 A hA
  obtain ⟨h, hres'⟩ := hcrit _ hf ⟨k, hu⟩
  exact ⟨h, by rw [ComponentChart.comap_residue_apply]; exact hres'⟩

end Sign

theorem zeroSeries_eq_one_of_t_eq_one (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : zeroSeries Φ l = 1 := by
  have h1 : (Φ.tRat l : LaurentSeries ℚ) = 1 := by
    have h2 : coeffEmb (AlgebraicClosure ℚ) (Φ.tRat l : LaurentSeries ℚ) = 1 := by
      have := congrArg Subtype.val (Φ.t_eq l)
      rw [h] at this
      exact this.symm
    exact (coeffEmb (AlgebraicClosure ℚ)).injective (by rw [h2, map_one])
  have h3 : Φ.tRat l = 1 := Subtype.ext h1
  rw [zeroSeries, h3, map_one]
  rfl

theorem isContent_zero_of_t_eq_one (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : IsContent Φ l 0 := by
  rw [IsContent, zeroSeries_eq_one_of_t_eq_one Φ l h]
  refine ⟨fun k hk => ?_, 0, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · subst hk0; rw [HahnSeries.coeff_one]; simp
    · exfalso; apply hk; rw [HahnSeries.coeff_one]; simp [hk0]
  · rw [HahnSeries.coeff_one]; simp
  · rw [HahnSeries.coeff_one]; simp

theorem hasseExp_eq_zero_of_t_eq_one (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : hasseExp Φ l = 0 := by
  rw [hasseExp, hasseContent_eq_of_isContent (isContent_zero_of_t_eq_one Φ l h)]
  rfl

section Keyed

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)

theorem infChart_mem_integers_iff (g : modularFunctionFieldBar (1 * p)) :
    g ∈ (infChart Γ).integers ↔ (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A) := by
  show g ∈ (chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply).integers ↔ _
  rw [chartFst_integers]
  exact mem_integersFst_iff_coe_mem_modularLocalized Γ.R g

theorem infChart_residue_eq_modularRedLocHom' (g : modularFunctionFieldBar (1 * p))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)) :
    ∃ h : g ∈ (infChart Γ).integers,
      (((infChart Γ).residue ⟨g, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
        = CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hg⟩ :=
  chartFst_residue_eq_modularRedLocHom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply g hg

theorem infChart_mem_nodes_iff (x : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
    x ∈ (infChart Γ).nodes ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x :=
  mem_chartFst_nodes_iff Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply x

theorem infChart_criterion (g : modularFunctionFieldBar (1 * p))
    (hf : ∀ k : ℤ, (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A)
    (hu : ∃ k : ℤ, IsUnit (⟨(g : LaurentSeries (AlgebraicClosure ℚ)).coeff k, hf k⟩ : ↥A)) :
    ∃ h : g ∈ (infChart Γ).integers, (infChart Γ).residue ⟨g, h⟩ ≠ 0 :=
  chartFst_mem_integers_residue_ne_zero_of_qCoeff Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply g hf hu

theorem cuspZeroBar_not_mem_infChart_dom' : cuspZeroBar (1 * p) ∉ (infChart Γ).dom :=
  cuspZeroBar_not_mem_infChart_dom Γ

theorem t_ne_zero (l : Fin r) : Φ.t l ≠ 0 := Φ.t_basis.1.ne_zero l

theorem t_mem_riemannRochSpace (l : Fin r) : Φ.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← Φ.t_basis.2]
  exact Submodule.subset_span ⟨l, rfl⟩

theorem t_pole (l : Fin r) :
    ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p) := by
  intro W hW
  by_contra hne
  have h := (mem_riemannRochSpace_iff.mp (t_mem_riemannRochSpace p Φ l)) W
  rcases h with h | h
  · exact t_ne_zero p Φ l h
  · have : (embDivisor (1 * p)) W = 0 := by
      show ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) W = 0
      rw [Finsupp.smul_apply]
      first
      | rw [Finsupp.single_eq_of_ne hne, smul_zero]
      | rw [Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]
    rw [this, neg_zero] at h
    omega

include hA in

theorem exists_isContent_goodFamily (l : Fin r) : ∃ n : ℤ, IsContent Φ.toFamData l n := by
  obtain ⟨c, hc0, hcA⟩ := exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar p
    (embDegree (1 * p)) (Φ.t l) (t_mem_riemannRochSpace p Φ l) (t_ne_zero p Φ l) A hA
  exact exists_isContent Φ.toFamData l (t_ne_zero p Φ l) A hA c hc0 hcA

include hA in

theorem hasValue_zero_infChart_residue (l : Fin r) (hl : 1 ≤ (l : ℕ)) (hint : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (P : Fin r → Polynomial (ResidueField ↥A))
    (hP : (infChart Γ).residue ⟨Φ.t l, hint l⟩
      = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l))
    (e : Fin (mAnnuli p)) :
    (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).HasValue ((infChart Γ).residue ⟨Φ.t l, hint l⟩) 0 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  set v := charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e) with hv
  have hvrat : v.IsRational := isRational_place_modularFunctionFieldC_one (ResidueField ↥A) v

  have hfac : ∀ c : ResidueField ↥A, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) ∈ v.toValuationSubring := by
    intro c
    by_cases h0 : (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) = 0
    · rw [h0]; exact zero_mem _
    · apply Place.mem_of_ord_nonneg _ h0
      rw [hv, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap]
      split_ifs <;> omega
  have hj0 : v.HasValue (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) 0 := by
    rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, map_zero, sub_zero]
    refine ⟨hfac _, ?_⟩
    by_cases h0 : (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) = 0
    · exact Or.inl h0
    · right; rw [hv, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, if_pos rfl]; exact zero_lt_one

  have hjmem : jBar (ResidueField ↥A) ∈ v.toValuationSubring := by
    have := add_mem (hfac (ssValue Γ e)) (v.algebraMap_mem' (ssValue Γ e))
    rwa [sub_add_cancel] at this
  have haeval : ∀ Q : Polynomial (ResidueField ↥A), Polynomial.aeval (jBar (ResidueField ↥A)) Q ∈ v.toValuationSubring := by
    intro Q
    rw [Polynomial.aeval_eq_sum_range]
    refine sum_mem fun n _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' _) (pow_mem hjmem n)

  have hrest : (∏ e' ∈ Finset.univ.erase e, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e'))) ∈ v.toValuationSubring :=
    prod_mem fun e' _ => hfac _
  obtain ⟨r₁, hr₁, -⟩ := v.exists_hasValue_of_surjective hvrat hrest
  obtain ⟨r₂, hr₂, -⟩ := v.exists_hasValue_of_surjective hvrat (haeval (P l))
  have hss : v.HasValue (ssPolyBar Γ) 0 := by
    have hsplit : ssPolyBar Γ = (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) *
        ∏ e' ∈ Finset.univ.erase e, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e')) := by
      show (∏ e' : Fin (mAnnuli p), (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e'))) = _
      exact (Finset.mul_prod_erase (Finset.univ)
        (fun e' => jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e')) (Finset.mem_univ e)).symm
    rw [hsplit]
    have := hj0.mul hr₁
    rwa [zero_mul] at this
  rw [hP]
  have := hss.mul hr₂
  rwa [zero_mul] at this

include hA Γ in

theorem hasseContent_nonneg (l : Fin r) : 0 ≤ hasseContent Φ.toFamData l := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨hint, -, -⟩ := Φ.t_inf A hA Γ
  exact hasseContent_nonneg_of_chart A hA (infChart Γ) (infChart_mem_integers_iff p A Γ)
    (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
    (cuspZeroBar_not_mem_infChart_dom' p A Γ) (infChart_criterion p A Γ)
    Φ.toFamData l (exists_isContent_goodFamily p A hA Φ l) (t_ne_zero p Φ l) (hint l) (t_pole p Φ l)

include hA Γ in
theorem hasseExp_eq_hasseContent (l : Fin r) : (hasseExp Φ.toFamData l : ℤ) = hasseContent Φ.toFamData l :=
  hasseExp_cast Φ.toFamData l (hasseContent_nonneg p A hA Γ Φ l)

include hA in

theorem zeroChart_residue_goodFamilyZero_ne_zero :
    ∃ hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers,
      ∀ i, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩ ≠ 0 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨hint, -, -⟩ := Φ.t_inf A hA Γ
  have key : ∀ i, ∃ h : goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, h⟩ ≠ 0 := fun i =>
    goodFamilyZero_mem_comap_integers_residue_ne_zero_of_chart A hA (infChart Γ) (infChart_mem_integers_iff p A Γ)
      (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
      (cuspZeroBar_not_mem_infChart_dom' p A Γ) (infChart_criterion p A Γ)
      Φ.toFamData i (exists_isContent_goodFamily p A hA Φ i) (t_ne_zero p Φ i) (hint i) (t_pole p Φ i)
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

include hA in

theorem goodFamilyZero_mem_zeroChart_integers : ∀ l : Fin r, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers :=
  (zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ).1

include hA Γ in

theorem one_le_hasseExp : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  intro l hl
  obtain ⟨hint, -, P, hP, -, -⟩ := Φ.t_inf A hA Γ
  obtain ⟨a, ha⟩ := ssJSet_nonempty (q := p) (k := ResidueField ↥A)
  obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
  have hval := hasValue_zero_infChart_residue p A hA Γ Φ l hl hint P (hP l hl).2 e
  refine one_le_hasseExp_of_chart A hA (infChart Γ) (infChart_mem_integers_iff p A Γ)
    (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
    (cuspZeroBar_not_mem_infChart_dom' p A Γ) (infChart_criterion p A Γ)
    Φ.toFamData l (exists_isContent_goodFamily p A hA Φ l) (t_ne_zero p Φ l) (hint l) (t_pole p Φ l)
    ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, hval⟩

theorem hasseExp_zero : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp Φ.toFamData l = 0 := fun l hl =>
  hasseExp_eq_zero_of_t_eq_one Φ.toFamData l (Φ.t_zero l hl)

end Keyed

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero.ModularCurve IsLocalRing Polynomial"

section CdwTools
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ord_pt_jBar_sub (x c : (IsLocalRing.ResidueField ↥A)) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = if c = x then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (IsLocalRing.ResidueField ↥A) x c

theorem aeval_jBar_eq_zero {Q : Polynomial (IsLocalRing.ResidueField ↥A)} (h : aeval (jBar (IsLocalRing.ResidueField ↥A)) Q = 0) : Q = 0 := by
  by_contra hQ
  have e : aeval (jqModC (IsLocalRing.ResidueField ↥A)) Q = (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (aeval (jBar (IsLocalRing.ResidueField ↥A)) Q) :=
    Polynomial.aeval_algHom_apply (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (jBar (IsLocalRing.ResidueField ↥A)) Q
  rw [h, _root_.map_zero] at e
  exact ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField ↥A) ⟨Q, hQ, e⟩

theorem aeval_jBar_injective' {Q₁ Q₂ : Polynomial (IsLocalRing.ResidueField ↥A)} (h : aeval (jBar (IsLocalRing.ResidueField ↥A)) Q₁ = aeval (jBar (IsLocalRing.ResidueField ↥A)) Q₂) :
    Q₁ = Q₂ :=
  sub_eq_zero.mp (aeval_jBar_eq_zero (by rw [_root_.map_sub, h, sub_self]))

theorem ord_placeInfty_jBar_sub [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] (c : (IsLocalRing.ResidueField ↥A)) :
    (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = -1 := by
  set v := charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) with hv
  have hJ : v.ord (jBar (IsLocalRing.ResidueField ↥A)) = -1 := ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (IsLocalRing.ResidueField ↥A)
  by_cases hc : c = 0
  · rw [hc, _root_.map_zero, sub_zero]; exact hJ
  have hC0 : algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hCord : v.ord (algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = 0 := Place.ord_algebraMap v c
  have hnC : v.ord (-algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c) = 0 := by
    rw [← _root_.map_neg]; exact Place.ord_algebraMap v (-c)
  have hJ0 : jBar (IsLocalRing.ResidueField ↥A) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hJ; norm_num at hJ
  have hsub0 : jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c ≠ 0 := by
    intro h0
    have : v.ord (jBar (IsLocalRing.ResidueField ↥A)) = 0 := by rw [sub_eq_zero.mp h0]; exact hCord
    rw [hJ] at this; norm_num at this

  have h1 := Place.min_ord_le_ord_add v hJ0 ((neg_ne_zero).mpr hC0) (by rw [← sub_eq_add_neg]; exact hsub0)
  rw [← sub_eq_add_neg, hJ, hnC] at h1

  have h2 := Place.min_ord_le_ord_add v hsub0 hC0 (by rw [sub_add_cancel]; exact hJ0)
  rw [sub_add_cancel, hJ, hCord] at h2
  omega

include Γ in

theorem exists_ssValue_ne [IsAlgClosed (IsLocalRing.ResidueField ↥A)] (hp13 : 13 ≤ p) :
    ∃ e : Fin (mAnnuli p), ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728 := by
  classical
  by_contra hall
  push_neg at hall
  have hinj := ssValue_injective Γ
  set f0 : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => ssValue Γ e = 0) with hf0
  set f1 : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => ssValue Γ e = 1728) with hf1
  have hcov : (Finset.univ : Finset (Fin (mAnnuli p))) ⊆ f0 ∪ f1 := by
    intro e _
    rw [Finset.mem_union, hf0, hf1, Finset.mem_filter, Finset.mem_filter]
    by_cases h0 : ssValue Γ e = 0
    · exact Or.inl ⟨Finset.mem_univ _, h0⟩
    · exact Or.inr ⟨Finset.mem_univ _, hall e h0⟩
  have h0card : f0.card ≤ (if p % 3 = 2 then 1 else 0) := by
    split_ifs with h3
    · refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      rw [hf0, Finset.mem_filter] at ha hb
      exact hinj (ha.2.trans hb.2.symm)
    · rw [Nat.le_zero, Finset.card_eq_zero, hf0, Finset.filter_eq_empty_iff]
      intro e _ he
      have hmem : (0 : (IsLocalRing.ResidueField ↥A)) ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := by rw [← he]; exact ssValue_mem_ssJSet Γ e
      exact h3 ((ModularCurve.zero_mem_ssJSet_iff p (by omega) (IsLocalRing.ResidueField ↥A)).mp hmem)
  have h1card : f1.card ≤ (if p % 4 = 3 then 1 else 0) := by
    split_ifs with h4
    · refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      rw [hf1, Finset.mem_filter] at ha hb
      exact hinj (ha.2.trans hb.2.symm)
    · rw [Nat.le_zero, Finset.card_eq_zero, hf1, Finset.filter_eq_empty_iff]
      intro e _ he
      have hmem : (1728 : (IsLocalRing.ResidueField ↥A)) ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := by rw [← he]; exact ssValue_mem_ssJSet Γ e
      exact h4 ((ModularCurve.ofNat1728_mem_ssJSet_iff p (by omega) (IsLocalRing.ResidueField ↥A)).mp hmem)
  have hle : mAnnuli p ≤ f0.card + f1.card := by
    calc mAnnuli p = (Finset.univ : Finset (Fin (mAnnuli p))).card := by simp
      _ ≤ (f0 ∪ f1).card := Finset.card_le_card hcov
      _ ≤ f0.card + f1.card := Finset.card_union_le _ _
  have hp12 : 1 ≤ p / 12 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hfin : mAnnuli p ≤ (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0) :=
    hle.trans (add_le_add h0card h1card)
  unfold mAnnuli at hfin
  split_ifs at hfin <;> omega

end CdwTools

section Descent

theorem exists_natCast_eq_of_pow_eq_self {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    {x : k} (hx : x ^ p = x) : ∃ m : ℕ, m < p ∧ (m : k) = x := by
  classical

  set f : Polynomial k := Polynomial.X ^ p - Polynomial.X with hf
  have hp1 : 1 < p := hp.out.one_lt
  have hf0 : f ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hf, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; exact hp1), Polynomial.natDegree_X_pow,
      Polynomial.natDegree_zero] at this
    exact hp.out.ne_zero this
  have hroot : ∀ y : k, y ^ p = y → y ∈ f.roots := by
    intro y hy
    rw [Polynomial.mem_roots hf0, Polynomial.IsRoot, hf, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hy, sub_self]
  have hnat : ∀ m : ℕ, ((m : k)) ^ p = (m : k) := fun m => by
    rw [← frobenius_def, map_natCast]

  set S : Finset k := Finset.univ.image (fun m : Fin p => ((m : ℕ) : k)) with hS
  have hinj : Function.Injective (fun m : Fin p => ((m : ℕ) : k)) := by
    intro a b hab
    have h := (CharP.natCast_eq_natCast (R := k) p).mp hab
    exact Fin.ext (by
      have ha := a.isLt; have hb := b.isLt
      rw [Nat.ModEq] at h
      rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h)
  have hScard : S.card = p := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hSsub : S ⊆ f.roots.toFinset := by
    intro y hy
    rw [hS, Finset.mem_image] at hy
    obtain ⟨m, -, rfl⟩ := hy
    rw [Multiset.mem_toFinset]
    exact hroot _ (hnat m)
  have hcard : f.roots.toFinset.card ≤ p := by
    calc f.roots.toFinset.card ≤ Multiset.card f.roots := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = p := by
        rw [hf, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
          rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]; exact hp1), Polynomial.natDegree_X_pow]
  have hSeq : S = f.roots.toFinset := Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hcard)
  have hxS : x ∈ S := by rw [hSeq, Multiset.mem_toFinset]; exact hroot x hx
  rw [hS, Finset.mem_image] at hxS
  obtain ⟨m, -, hm⟩ := hxS
  exact ⟨m, m.isLt, hm⟩

theorem pow_eq_self_of_semilinear_fixed {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {M : Type*} [AddCommGroup M] [Module k M] (σ : M →+ M) (hσ : ∀ (c : k) (x : M), σ (c • x) = c ^ p • σ x)
    {ι : Type*} [Fintype ι] (f : ι → M) (hf : LinearIndependent k f) (hfix : ∀ i, σ (f i) = f i)
    (c : ι → k) (hh : σ (∑ i, c i • f i) = ∑ i, c i • f i) : ∀ i, c i ^ p = c i := by
  have h1 : σ (∑ i, c i • f i) = ∑ i, c i ^ p • f i := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hσ, hfix])
  have h2 : ∑ i, (c i ^ p - c i) • f i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h1, hh, sub_self]
  have h3 := linearIndependent_iff'.mp hf Finset.univ (fun i => c i ^ p - c i) h2
  intro i
  exact sub_eq_zero.mp (h3 i (Finset.mem_univ i))

end Descent

section PlaceMore

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_neg' (v : Place K F) (g : F) : v.ord (-g) = v.ord g := by
  by_cases hg : g = 0
  · rw [hg, neg_zero]
  rw [show -g = algebraMap K F (-1) * g by rw [map_neg, map_one]; ring,
    v.ord_mul ((_root_.map_ne_zero _).mpr (by norm_num)) hg, Place.ord_algebraMap, zero_add]

theorem ord_add_eq_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  by_cases hg : g = 0
  · rw [hg, add_zero]
  have hfg : f + g ≠ 0 := by
    intro h0
    have : f = -g := eq_neg_of_add_eq_zero_left h0
    rw [this, ord_neg'] at h
    exact lt_irrefl _ h
  have h1 := Place.min_ord_le_ord_add v hf hg hfg
  have h2 : f = (f + g) + (-g) := by ring
  have h3 := Place.min_ord_le_ord_add v hfg (neg_ne_zero.mpr hg) (by rw [← h2]; exact hf)
  rw [← h2, ord_neg'] at h3
  omega

theorem ord_sum_ge (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (n : ℤ)
    (h : ∀ i ∈ s, f i = 0 ∨ n ≤ v.ord (f i)) : (∑ i ∈ s, f i) = 0 ∨ n ≤ v.ord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have iha := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hfa := h a (Finset.mem_insert_self a s)
    by_cases h0 : f a + ∑ i ∈ s, f i = 0
    · left; exact h0
    right
    rcases hfa with hfa | hfa
    · rw [hfa, zero_add] at h0 ⊢
      rcases iha with h1 | h1
      · exact absurd h1 h0
      · exact h1
    rcases iha with h1 | h1
    · rw [h1, add_zero]; exact hfa
    · by_cases hfa0 : f a = 0
      · rw [hfa0, zero_add]; exact h1
      by_cases hs0 : ∑ i ∈ s, f i = 0
      · rw [hs0, add_zero]; exact hfa
      exact (le_min hfa h1).trans (Place.min_ord_le_ord_add v hfa0 hs0 h0)

theorem ord_finset_prod (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem hasValue_evalAt (v : Place K F) (hv : v.IsRational) {g : F} (hg : g ∈ v.toValuationSubring) :
    v.HasValue g (v.evalAt g) :=
  ⟨hg, (v.algebraMap_evalAt hv hg).symm⟩

end PlaceMore

section HFun

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

open P2MF2J

noncomputable def wOne : Finset (IsLocalRing.ResidueField ↥A) :=
  (Finset.univ.image (ssValue Γ)).filter (fun b => jWidth b = 1)

theorem mem_wOne {b : (IsLocalRing.ResidueField ↥A)} : b ∈ wOne Γ ↔ (∃ e, ssValue Γ e = b) ∧ jWidth b = 1 := by
  unfold wOne
  rw [Finset.mem_filter, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]

theorem mem_ssJSet_of_mem_wOne {b : (IsLocalRing.ResidueField ↥A)} (hb : b ∈ wOne Γ) : b ∈ ssJSet p (IsLocalRing.ResidueField ↥A) := by
  obtain ⟨⟨e, rfl⟩, -⟩ := (mem_wOne Γ).mp hb
  exact ssValue_mem_ssJSet Γ e

theorem ne_zero_of_mem_wOne {b : (IsLocalRing.ResidueField ↥A)} (hb : b ∈ wOne Γ) : b ≠ 0 := by
  intro h0
  have h := ((mem_wOne Γ).mp hb).2
  rw [h0, jWidth_of_eq_zero rfl] at h
  exact absurd h (by decide)

theorem zero_not_mem_wOne : (0 : (IsLocalRing.ResidueField ↥A)) ∉ wOne Γ := fun h => ne_zero_of_mem_wOne Γ h rfl

theorem pow_mem_wOne [IsAlgClosed (IsLocalRing.ResidueField ↥A)] {b : (IsLocalRing.ResidueField ↥A)} (hb : b ∈ wOne Γ) : b ^ p ∈ wOne Γ := by
  obtain ⟨⟨e, rfl⟩, hw⟩ := (mem_wOne Γ).mp hb
  rw [mem_wOne]
  refine ⟨?_, ?_⟩
  · have hmem : ssValue Γ e ^ p ∈ ssJSet p (IsLocalRing.ResidueField ↥A) :=
      (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p (ssValue Γ e)).mpr (ssValue_mem_ssJSet Γ e)
    exact exists_ssValue_eq Γ _ hmem
  · rw [← frobenius_def, jWidth_map]; exact hw

theorem charLGeomPlaceOfPoint_mem_nodes_of_mem_wOne [IsAlgClosed (IsLocalRing.ResidueField ↥A)] {b : (IsLocalRing.ResidueField ↥A)} (hb : b ∈ wOne Γ) :
    charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) b ∈ (zeroChart Γ).nodes := by
  rw [mem_zeroChart_nodes_iff]
  have hss := mem_ssJSet_of_mem_wOne Γ hb
  refine ⟨b ^ p, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField p b).mpr hss, ?_⟩
  rw [← pow_mul, ← pow_two, ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet p hss]

include Γ in

theorem wOne_nonempty [IsAlgClosed (IsLocalRing.ResidueField ↥A)] (hp13 : 13 ≤ p) : (wOne Γ).Nonempty := by
  obtain ⟨e, h0, h1728⟩ := exists_ssValue_ne Γ hp13
  exact ⟨ssValue Γ e, (mem_wOne Γ).mpr ⟨⟨e, rfl⟩, jWidth_of_ne h0 h1728⟩⟩

noncomputable def polW : Polynomial (IsLocalRing.ResidueField ↥A) := ∏ b ∈ wOne Γ, (Polynomial.X - Polynomial.C b)

theorem polW_monic : (polW Γ).Monic := by
  unfold polW; exact Polynomial.monic_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C b

theorem polW_ne_zero : polW Γ ≠ 0 := (polW_monic Γ).ne_zero

theorem polW_natDegree : (polW Γ).natDegree = (wOne Γ).card := by
  unfold polW
  rw [Polynomial.natDegree_prod_of_monic _ _ fun b _ => Polynomial.monic_X_sub_C b]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem polW_eval (x : (IsLocalRing.ResidueField ↥A)) : (polW Γ).eval x = ∏ b ∈ wOne Γ, (x - b) := by
  unfold polW; rw [Polynomial.eval_prod]; simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem polW_eval_ne_zero {x : (IsLocalRing.ResidueField ↥A)} (hx : x ∉ wOne Γ) : (polW Γ).eval x ≠ 0 := by
  rw [polW_eval, Finset.prod_ne_zero_iff]
  intro b hb; exact sub_ne_zero.mpr (fun h => hx (h ▸ hb))

theorem rootMultiplicity_polW (x : (IsLocalRing.ResidueField ↥A)) :
    (polW Γ).rootMultiplicity x = if x ∈ wOne Γ then 1 else 0 := by
  classical
  split_ifs with hx
  · have hsplit : polW Γ = (Polynomial.X - Polynomial.C x) * ∏ b ∈ (wOne Γ).erase x, (Polynomial.X - Polynomial.C b) := by
      unfold polW; exact (Finset.mul_prod_erase (wOne Γ) (fun b => Polynomial.X - Polynomial.C b) hx).symm
    have hrest : (∏ b ∈ (wOne Γ).erase x, (Polynomial.X - Polynomial.C b)).eval x ≠ 0 := by
      rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro b hb
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
    have hne : (Polynomial.X - Polynomial.C x) * ∏ b ∈ (wOne Γ).erase x, (Polynomial.X - Polynomial.C b) ≠ 0 :=
      mul_ne_zero (Polynomial.X_sub_C_ne_zero x) (fun h => hrest (by rw [h, Polynomial.eval_zero]))
    rw [hsplit, Polynomial.rootMultiplicity_mul hne, Polynomial.rootMultiplicity_X_sub_C_self,
      Polynomial.rootMultiplicity_eq_zero (fun h : Polynomial.IsRoot _ x => hrest h)]
  · exact Polynomial.rootMultiplicity_eq_zero (fun h : Polynomial.IsRoot _ x => polW_eval_ne_zero Γ hx h)

theorem polW_map_frobenius [IsAlgClosed (IsLocalRing.ResidueField ↥A)] : (polW Γ).map (frobenius (IsLocalRing.ResidueField ↥A) p) = polW Γ := by
  classical
  unfold polW
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

  have hinj : Set.InjOn (frobenius (IsLocalRing.ResidueField ↥A) p) (wOne Γ) := fun a _ b _ h => frobenius_inj (IsLocalRing.ResidueField ↥A) p h
  have himage : (wOne Γ).image (frobenius (IsLocalRing.ResidueField ↥A) p) = wOne Γ := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      rw [frobenius_def]; exact pow_mem_wOne Γ hb
    · rw [Finset.card_image_of_injOn hinj]
  calc ∏ b ∈ wOne Γ, (Polynomial.X - Polynomial.C (frobenius (IsLocalRing.ResidueField ↥A) p b))
      = ∏ y ∈ (wOne Γ).image (frobenius (IsLocalRing.ResidueField ↥A) p), (Polynomial.X - Polynomial.C y) :=
        (Finset.prod_image (f := fun y => Polynomial.X - Polynomial.C y) (fun a ha b hb h => hinj ha hb h)).symm
    _ = ∏ b ∈ wOne Γ, (Polynomial.X - Polynomial.C b) := by rw [himage]

noncomputable def hfun : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  1 + (jB (IsLocalRing.ResidueField ↥A)) ^ (wOne Γ).card * (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ))⁻¹

noncomputable def gfun : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := (jB (IsLocalRing.ResidueField ↥A)) ^ (wOne Γ).card * (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ))⁻¹

theorem hfun_eq : hfun Γ = 1 + gfun Γ := rfl

theorem aeval_polW_ne_zero : Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ) ≠ 0 := aeval_jB_ne_zero (IsLocalRing.ResidueField ↥A) _ (polW_ne_zero Γ)

theorem jB_ne_zero : jB (IsLocalRing.ResidueField ↥A) ≠ 0 := by
  have := aeval_jB_ne_zero (IsLocalRing.ResidueField ↥A) Polynomial.X Polynomial.X_ne_zero
  rwa [Polynomial.aeval_X] at this

theorem gfun_ne_zero : gfun Γ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (jB_ne_zero)) (inv_ne_zero (aeval_polW_ne_zero Γ))

theorem ord_pt_gfun (x : (IsLocalRing.ResidueField ↥A)) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (gfun Γ)
      = ((wOne Γ).card : ℤ) * (if (0 : (IsLocalRing.ResidueField ↥A)) = x then 1 else 0) - (if x ∈ wOne Γ then 1 else 0) := by
  unfold gfun
  rw [(charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord_mul (pow_ne_zero _ jB_ne_zero) (inv_ne_zero (aeval_polW_ne_zero Γ)),
    Place.ord_inv, ← zpow_natCast, Place.ord_zpow, ord_charLGeomPlaceOfPoint_aeval (IsLocalRing.ResidueField ↥A) x _ (polW_ne_zero Γ),
    rootMultiplicity_polW]
  have hj : (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (jB (IsLocalRing.ResidueField ↥A)) = if (0 : (IsLocalRing.ResidueField ↥A)) = x then 1 else 0 := by
    have := ord_pt_jBar_sub (A := A) x 0
    rwa [_root_.map_zero, sub_zero] at this
  rw [hj]
  push_cast
  split_ifs <;> ring

theorem ord_infty_gfun [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] : (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (gfun Γ) = 0 := by
  unfold gfun
  rw [(charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord_mul (pow_ne_zero _ jB_ne_zero) (inv_ne_zero (aeval_polW_ne_zero Γ)),
    Place.ord_inv, ← zpow_natCast, Place.ord_zpow]
  have hj : (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (jB (IsLocalRing.ResidueField ↥A)) = -1 := ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (IsLocalRing.ResidueField ↥A)
  have hD : (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ)) = -((wOne Γ).card : ℤ) := by
    unfold polW
    rw [_root_.map_prod]
    simp only [_root_.map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [ord_finset_prod _ _ _ (fun b _ => ?_)]
    · simp only [ord_placeInfty_jBar_sub, Finset.sum_const, smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one]
    · have := ord_pt_jBar_sub (A := A) b b
      intro h0
      rw [h0, Place.ord_zero, if_pos rfl] at this
      exact absurd this (by norm_num)
  rw [hj, hD]; ring

theorem ord_pt_hfun_of_mem {x : (IsLocalRing.ResidueField ↥A)} (hx : x ∈ wOne Γ) : (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (hfun Γ) = -1 := by
  have hx0 : (0 : (IsLocalRing.ResidueField ↥A)) ≠ x := fun h => zero_not_mem_wOne Γ (h ▸ hx)
  have hG : (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (gfun Γ) = -1 := by
    rw [ord_pt_gfun, if_neg hx0, if_pos hx]; ring
  rw [hfun_eq, add_comm, ord_add_eq_of_lt _ (gfun_ne_zero Γ) (by rw [hG, Place.ord_one]; norm_num), hG]

theorem ord_pt_hfun_zero (hN : 0 < (wOne Γ).card) : (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) 0).ord (hfun Γ) = 0 := by
  have hG : (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (0 : (IsLocalRing.ResidueField ↥A))).ord (gfun Γ) = (wOne Γ).card := by
    rw [ord_pt_gfun, if_pos rfl, if_neg (zero_not_mem_wOne Γ)]; ring
  rw [hfun_eq, ord_add_eq_of_lt _ one_ne_zero (by rw [hG, Place.ord_one]; exact_mod_cast hN), Place.ord_one]

theorem ord_hfun_nonneg_of (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) (hG : 0 ≤ v.ord (gfun Γ)) : 0 ≤ v.ord (hfun Γ) := by
  rw [hfun_eq]
  by_cases h0 : (1 : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) + gfun Γ = 0
  · rw [h0, Place.ord_zero]
  have := Place.min_ord_le_ord_add v one_ne_zero (gfun_ne_zero Γ) h0
  rw [Place.ord_one] at this
  exact le_trans (le_min le_rfl hG) this

theorem ord_pt_hfun_nonneg {x : (IsLocalRing.ResidueField ↥A)} (hx : x ∉ wOne Γ) : 0 ≤ (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).ord (hfun Γ) := by
  apply ord_hfun_nonneg_of
  rw [ord_pt_gfun, if_neg hx]
  split_ifs <;> simp

theorem ord_infty_hfun_nonneg [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] : 0 ≤ (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (hfun Γ) :=
  ord_hfun_nonneg_of Γ _ (by rw [ord_infty_gfun])

theorem hfun_hreg [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] :
    ∀ v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord (hfun Γ) := by
  intro v hv
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A) v with ⟨x, rfl⟩ | rfl
  · exact ord_pt_hfun_nonneg Γ (fun hx => hv (charLGeomPlaceOfPoint_mem_nodes_of_mem_wOne Γ hx))
  · exact ord_infty_hfun_nonneg Γ

theorem hfun_hnode [IsAlgClosed (IsLocalRing.ResidueField ↥A)] :
    ∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord (hfun Γ) := by
  intro e
  show _ ≤ (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p)).ord (hfun Γ)
  by_cases hw : jWidth (ssValue Γ e) = 1
  · have hmem : ssValue Γ e ^ p ∈ wOne Γ := pow_mem_wOne Γ ((mem_wOne Γ).mpr ⟨⟨e, rfl⟩, hw⟩)
    rw [ord_pt_hfun_of_mem Γ hmem, hw]; norm_num
  · have hnot : ssValue Γ e ^ p ∉ wOne Γ := by
      intro hmem
      have h1 := ((mem_wOne Γ).mp hmem).2
      rw [← frobenius_def, jWidth_map] at h1
      exact hw h1
    exact le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (ord_pt_hfun_nonneg Γ hnot)

theorem hasValue_pt_hfun {x : (IsLocalRing.ResidueField ↥A)} (hx : x ∉ wOne Γ) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x).HasValue (hfun Γ) (1 + x ^ (wOne Γ).card * ((polW Γ).eval x)⁻¹) := by
  rw [hfun_eq]
  refine P2MF2J.HasValue.add (Place.hasValue_one _) ?_
  unfold gfun
  rw [← Polynomial.aeval_X_pow (R := (IsLocalRing.ResidueField ↥A)) (jB (IsLocalRing.ResidueField ↥A))]
  have := hasValue_aeval_mul_inv (IsLocalRing.ResidueField ↥A) x (Polynomial.X ^ (wOne Γ).card) (polW Γ) (polW_eval_ne_zero Γ hx)
  rwa [Polynomial.eval_pow, Polynomial.eval_X] at this

theorem hasValue_infty_hfun [IsAlgClosed (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] (hN : 0 < (wOne Γ).card) :
    (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).HasValue (hfun Γ) 2 := by
  rw [hfun_eq, show (2 : (IsLocalRing.ResidueField ↥A)) = 1 + 1 by norm_num]
  refine P2MF2J.HasValue.add (Place.hasValue_one _) ?_

  set N := (wOne Γ).card with hN'
  by_cases hXD : Polynomial.X ^ N - polW Γ = 0
  · have hG : gfun Γ = 1 := by
      unfold gfun
      have : (jB (IsLocalRing.ResidueField ↥A)) ^ N = Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ) := by
        have h0 : Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (Polynomial.X ^ N - polW Γ) = 0 := by rw [hXD, _root_.map_zero]
        rwa [_root_.map_sub, Polynomial.aeval_X_pow, sub_eq_zero] at h0
      rw [this, mul_inv_cancel₀ (aeval_polW_ne_zero Γ)]
    rw [hG]; exact Place.hasValue_one _
  apply hasValue_of_ord_sub_algebraMap_pos
  rw [_root_.map_one]
  have hsub : gfun Γ - 1 = Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (Polynomial.X ^ N - polW Γ) * (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ))⁻¹ := by
    unfold gfun
    rw [_root_.map_sub, Polynomial.aeval_X_pow, sub_mul, mul_inv_cancel₀ (aeval_polW_ne_zero Γ)]
  have hdeg : (Polynomial.X ^ N - polW Γ).natDegree < N := by
    have h1 : (Polynomial.X ^ N - polW Γ).degree < (N : WithBot ℕ) := by
      have := Polynomial.degree_sub_lt (p := Polynomial.X ^ N) (q := polW Γ)
        (by rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree (polW_ne_zero Γ), polW_natDegree])
        ((Polynomial.monic_X_pow N).ne_zero) (by rw [Polynomial.leadingCoeff_X_pow, (polW_monic Γ).leadingCoeff])
      rwa [Polynomial.degree_X_pow] at this
    exact (Polynomial.natDegree_lt_iff_degree_lt hXD).mpr h1

  have hlow : -((Polynomial.X ^ N - polW Γ).natDegree : ℤ)
      ≤ (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (Polynomial.X ^ N - polW Γ)) := by
    set Q := Polynomial.X ^ N - polW Γ with hQ
    have hsum := Q.as_sum_range_C_mul_X_pow
    have key := ord_sum_ge (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))) (Finset.range (Q.natDegree + 1))
      (fun i => Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (Polynomial.C (Q.coeff i) * Polynomial.X ^ i)) (-(Q.natDegree : ℤ))
      (fun i hi => by
        beta_reduce
        by_cases hc : Q.coeff i = 0
        · left; rw [hc, Polynomial.C_0, zero_mul, _root_.map_zero]
        right
        rw [_root_.map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
          (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord_mul ((_root_.map_ne_zero _).mpr hc) (pow_ne_zero _ jB_ne_zero), Place.ord_algebraMap,
          zero_add, ← zpow_natCast, Place.ord_zpow, ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC]
        have : i < Q.natDegree + 1 := Finset.mem_range.mp hi
        push_cast; omega)
    have heq : Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) Q = ∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (Polynomial.C (Q.coeff i) * Polynomial.X ^ i) := by
      conv_lhs => rw [hsum]
      rw [_root_.map_sum]
    rw [heq]
    rcases key with h0 | h0
    · exfalso; rw [← heq] at h0; exact aeval_jB_ne_zero (IsLocalRing.ResidueField ↥A) Q hXD h0
    · exact h0
  rw [hsub, (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord_mul (aeval_jB_ne_zero (IsLocalRing.ResidueField ↥A) _ hXD) (inv_ne_zero (aeval_polW_ne_zero Γ)), Place.ord_inv]
  have hD : (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ)) = -(N : ℤ) := by
    have := ord_infty_gfun Γ
    unfold gfun at this
    rw [(charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord_mul (pow_ne_zero _ jB_ne_zero) (inv_ne_zero (aeval_polW_ne_zero Γ)), Place.ord_inv,
      ← zpow_natCast, Place.ord_zpow, ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC] at this
    push_cast at this; omega
  rw [hD]; omega

theorem coeffMap_frobenius_hfun [IsAlgClosed (IsLocalRing.ResidueField ↥A)] :
    coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p) ((hfun Γ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = ((hfun Γ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) := by
  set σ := coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p) with hσ
  have hσj : σ (jqModC (IsLocalRing.ResidueField ↥A)) = jqModC (IsLocalRing.ResidueField ↥A) := coeffMap_jqModC _
  have hσc : ∀ c : (IsLocalRing.ResidueField ↥A), σ (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) c) = algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) (c ^ p) := by
    intro c
    rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, hσ, coeffMap_single, frobenius_def]
  have hσD : σ (Polynomial.aeval (jqModC (IsLocalRing.ResidueField ↥A)) (polW Γ)) = Polynomial.aeval (jqModC (IsLocalRing.ResidueField ↥A)) (polW Γ) := by
    conv_rhs => rw [← polW_map_frobenius Γ]
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂, hσj]
    congr 1
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [hσc, frobenius_def]

  have hcoe : ((hfun Γ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A))
      = 1 + (jqModC (IsLocalRing.ResidueField ↥A)) ^ (wOne Γ).card * (Polynomial.aeval (jqModC (IsLocalRing.ResidueField ↥A)) (polW Γ))⁻¹ := by
    unfold hfun
    have e1 : ((Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = Polynomial.aeval (jqModC (IsLocalRing.ResidueField ↥A)) (polW Γ) := by
      rw [show ((Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A))
          = (IntermediateField.val _) (Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (polW Γ)) from rfl, ← Polynomial.aeval_algHom_apply]
      rfl
    push_cast
    rw [e1]
  rw [hcoe, map_add, map_one, map_mul, map_pow, map_inv₀, hσj, hσD]

end HFun

section UMat

variable {r : ℕ} (u₀ T z : Fin r) (a : Fin r → ℚ) (b : ℚ)

def rowB : Fin r → ℚ := fun j => if j = T then 1 else if j = z then b else 0

def matU : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j => if i = u₀ then a j else if i = T then rowB T z b j else if i = j then 1 else 0

def matV : Matrix (Fin r) (Fin r) ℚ :=
  Matrix.of fun i j =>
    if i = u₀ then (if j = u₀ then (2 : ℚ) else 0) - a j + (if j = z then a T * b else 0)
    else if i = T then (if j = T then (2 : ℚ) else 0) - rowB T z b j
    else if i = j then 1 else 0

variable {u₀ T z a b}

theorem matU_apply_u0 (j : Fin r) : matU u₀ T z a b u₀ j = a j := by
  simp [matU]

theorem matU_apply_T (hTu : T ≠ u₀) (j : Fin r) : matU u₀ T z a b T j = rowB T z b j := by
  simp [matU, hTu]

theorem matU_apply_other {i : Fin r} (hiu : i ≠ u₀) (hiT : i ≠ T) (j : Fin r) :
    matU u₀ T z a b i j = if i = j then 1 else 0 := by
  simp [matU, hiu, hiT]

theorem matV_apply_u0 (j : Fin r) :
    matV u₀ T z a b u₀ j = (if j = u₀ then (2 : ℚ) else 0) - a j + (if j = z then a T * b else 0) := by
  simp [matV]

theorem matV_apply_T (hTu : T ≠ u₀) (j : Fin r) :
    matV u₀ T z a b T j = (if j = T then (2 : ℚ) else 0) - rowB T z b j := by
  simp [matV, hTu]

theorem matV_apply_other {i : Fin r} (hiu : i ≠ u₀) (hiT : i ≠ T) (j : Fin r) :
    matV u₀ T z a b i j = if i = j then 1 else 0 := by
  simp [matV, hiu, hiT]

theorem sum_split_two {M : Type*} [AddCommMonoid M] (f : Fin r → M) (huT : u₀ ≠ T) :
    ∑ k, f k = f u₀ + f T + ∑ k, (if k = u₀ ∨ k = T then 0 else f k) := by
  classical
  have hpt : ∀ k, f k = (if k = u₀ ∨ k = T then f k else 0) + (if k = u₀ ∨ k = T then 0 else f k) := by
    intro k; split_ifs <;> simp
  calc ∑ k, f k = ∑ k, ((if k = u₀ ∨ k = T then f k else 0) + (if k = u₀ ∨ k = T then 0 else f k)) :=
        Finset.sum_congr rfl (fun k _ => hpt k)
    _ = ∑ k, (if k = u₀ ∨ k = T then f k else 0) + ∑ k, (if k = u₀ ∨ k = T then 0 else f k) :=
        Finset.sum_add_distrib
    _ = f u₀ + f T + ∑ k, (if k = u₀ ∨ k = T then 0 else f k) := by
        congr 1
        rw [Fintype.sum_eq_add u₀ T huT (fun k hk => if_neg (not_or.mpr hk))]
        simp [huT, huT.symm]

theorem matU_mul_matV (huT : u₀ ≠ T) (huz : u₀ ≠ z) (hTz : T ≠ z) (hau : a u₀ = 1) :
    matU u₀ T z a b * matV u₀ T z a b = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hiu : i = u₀
  · subst hiu
    simp only [matU_apply_u0]
    rw [sum_split_two (u₀ := i) (T := T) _ huT, matV_apply_u0, matV_apply_T huT.symm]
    have hrest : ∑ k, (if k = i ∨ k = T then 0 else a k * matV i T z a b k j)
        = if j = i ∨ j = T then 0 else a j := by
      have hpt : ∀ k, (if k = i ∨ k = T then 0 else a k * matV i T z a b k j)
          = if k = j then (if j = i ∨ j = T then 0 else a j) else 0 := by
        intro k
        by_cases hk : k = i ∨ k = T
        · rw [if_pos hk]
          by_cases hkj : k = j
          · subst hkj; rw [if_pos rfl, if_pos hk]
          · rw [if_neg hkj]
        · rw [if_neg hk, matV_apply_other (not_or.mp hk).1 (not_or.mp hk).2]
          by_cases hkj : k = j
          · subst hkj; rw [if_pos rfl, if_pos rfl, if_neg hk, mul_one]
          · rw [if_neg hkj, if_neg hkj, mul_zero]
      rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j)]
    rw [hrest, hau, one_mul]
    simp only [rowB]
    by_cases hji : j = i
    · subst hji; norm_num [huT, huz, hau] <;> ring
    · by_cases hjT : j = T
      · subst hjT; norm_num [hji, Ne.symm hji, hTz] <;> ring
      · by_cases hjz : j = z
        · subst hjz; norm_num [hji, Ne.symm hji, hjT] <;> ring
        · norm_num [hji, hjT, hjz, Ne.symm hji] <;> ring
  · by_cases hiT : i = T
    · subst hiT
      simp only [matU_apply_T (Ne.symm huT)]
      rw [Fintype.sum_eq_add i z hTz (fun k hk => by
        simp only [rowB, if_neg hk.1, if_neg hk.2, zero_mul])]
      simp only [rowB, if_pos rfl, if_neg hTz.symm, matV_apply_T (Ne.symm huT), matV_apply_other huz.symm hTz.symm]
      by_cases hjT : j = i
      · subst hjT; norm_num [hTz, hTz.symm] <;> ring
      · by_cases hjz : j = z
        · subst hjz; norm_num [hjT, hTz.symm, Ne.symm hjT] <;> ring
        · norm_num [hjT, hjz, Ne.symm hjT, Ne.symm hjz] <;> ring
    · simp only [matU_apply_other hiu hiT]
      rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
        if_pos rfl, one_mul, matV_apply_other hiu hiT]

theorem isUnit_matU (huT : u₀ ≠ T) (huz : u₀ ≠ z) (hTz : T ≠ z) (hau : a u₀ = 1) :
    IsUnit (matU u₀ T z a b) := by
  have h := matU_mul_matV huT huz hTz hau (b := b)
  exact IsUnit.of_mul_eq_one _ h

theorem matU_inv (huT : u₀ ≠ T) (huz : u₀ ≠ z) (hTz : T ≠ z) (hau : a u₀ = 1) :
    (matU u₀ T z a b)⁻¹ = matV u₀ T z a b :=
  Matrix.inv_eq_right_inv (matU_mul_matV huT huz hTz hau)

end UMat

section SSPol
open Polynomial
variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ssPolyBar_eq_aeval' :
    ssPolyBar Γ = aeval (P2MF2J.jB (ResidueField ↥A)) (∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e))) := by
  rw [ssPolyBar, map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_sub, aeval_X, aeval_C]

theorem rootMultiplicity_prod_X_sub_C' (e : Fin (mAnnuli p)) :
    (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))).rootMultiplicity (ssValue Γ e) = 1 := by
  classical
  have hne : (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e' _ => X_sub_C_ne_zero _
  rw [← Polynomial.count_roots, Polynomial.roots_prod _ _ hne]
  simp only [Polynomial.roots_X_sub_C, Multiset.count_bind, Multiset.count_singleton]
  rw [show (Finset.univ.val.map fun e' : Fin (mAnnuli p) => if ssValue Γ e = ssValue Γ e' then 1 else 0).sum
      = ∑ e' : Fin (mAnnuli p), (if ssValue Γ e = ssValue Γ e' then 1 else 0) from rfl]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne'
    rw [if_neg]
    exact fun h => hne' ((ssValue_injective Γ) h).symm
  · simp

end SSPol

section Combo2

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

theorem coe_sum_smul_coeff (c : Fin r → ℚ) (X : Fin r → ↥(modularFunctionFieldFull (1 * p))) (m : ℤ) :
    (((∑ i, c i • X i : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m
      = ∑ i, c i * ((X i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
  have h1 : (((∑ i, c i • X i : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ)
      = ∑ i, (((c i • X i : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ) := by
    show (modularFunctionFieldFull (1 * p)).val (∑ i, c i • X i) = _
    rw [map_sum]; rfl
  rw [h1, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
  | rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul,
      HahnSeries.coeff_smul, smul_eq_mul]
  | rw [IntermediateField.coe_smul, HahnSeries.coeff_smul, smul_eq_mul]
  | (simp [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul]; done)
  | (simp [Algebra.smul_def];
     rw [← eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) (c i), algebraMap_laurentSeries_eq_single,
       HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul])

theorem hasseExp_eq_of_zeroSeries_eq {D₁ D₂ : FamData p r} {l₁ l₂ : Fin r}
    (h : zeroSeries D₁ l₁ = zeroSeries D₂ l₂) : hasseExp D₁ l₁ = hasseExp D₂ l₂ := by
  unfold hasseExp hasseContent
  rw [h]

theorem hasseExp_eq_of_isContent {D : FamData p r} {l : Fin r} {n : ℕ} (h : IsContent D l (n : ℤ)) :
    hasseExp D l = n := by
  unfold hasseExp
  rw [hasseContent_eq_of_isContent h, Int.toNat_natCast]

end Combo2

theorem residue_algebraMap_rat_eq_zero_of_padicValRat_pos' (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (q : ℚ) (hq : q ≠ 0)
    (hv : 1 ≤ padicValRat p q) (hmem : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A) :
    IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hmem⟩ = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  set q' : ℚ := q / p with hq'
  have hq'0 : q' ≠ 0 := div_ne_zero hq hp0
  have hqq' : q = p * q' := by rw [hq', mul_div_cancel₀ q hp0]
  have hvq' : 0 ≤ padicValRat p q' := by
    have h1 : padicValRat p q = padicValRat p (p : ℚ) + padicValRat p q' := by
      rw [hqq', padicValRat.mul hp0 hq'0]
    rw [padicValRat.self hp.one_lt] at h1
    linarith
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  have hq'A : ((q' : ℚ) : AlgebraicClosure ℚ) ∈ A :=
    (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq'0).2 hvq'
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(p : AlgebraicClosure ℚ), hpA⟩)).1 hA
  have e1 : (⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hmem⟩ : ↥A)
      = ⟨(p : AlgebraicClosure ℚ), hpA⟩ * ⟨((q' : ℚ) : AlgebraicClosure ℚ), hq'A⟩ := by
    apply Subtype.ext
    show algebraMap ℚ (AlgebraicClosure ℚ) q = (p : AlgebraicClosure ℚ) * ((q' : ℚ) : AlgebraicClosure ℚ)
    rw [eq_ratCast, hqq']; push_cast; ring
  rw [e1]
  exact (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_right _ _ hp𝔪)

section Combo

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

theorem chart_residue_sum (C : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ↥(modularFunctionFieldBar (1 * p))) (hg : ∀ j, g j ∈ C.integers) (y : ι → (AlgebraicClosure ℚ)) (hy : ∀ j, y j ∈ A) :
    ∃ h : (∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y j) * g j) ∈ C.integers,
      C.residue ⟨_, h⟩ = ∑ j, IsLocalRing.residue ↥A ⟨y j, hy j⟩ • C.residue ⟨g j, hg j⟩ := by
  set cj : ι → ↥C.integers := fun j => ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y j), (C.algebraMap_mem_iff _).mpr (hy j)⟩ with hcj
  set tj : ι → ↥C.integers := fun j => ⟨g j, hg j⟩ with htj
  have hval : ((∑ j, cj j * tj j : ↥C.integers) : ↥(modularFunctionFieldBar (1 * p))) = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y j) * g j := by
    push_cast; rfl
  have hmem : (∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (y j) * g j) ∈ C.integers := by
    rw [← hval]; exact (∑ j, cj j * tj j).2
  refine ⟨hmem, ?_⟩
  have heq : (⟨_, hmem⟩ : ↥C.integers) = ∑ j, cj j * tj j := Subtype.ext hval.symm
  rw [heq, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, Algebra.smul_def]
  congr 1
  exact C.residue_algebraMap ⟨y j, hy j⟩

theorem residueA_congr {x y : (AlgebraicClosure ℚ)} (hx : x ∈ A) (hy : y ∈ A) (h : x = y) :
    IsLocalRing.residue ↥A ⟨x, hx⟩ = IsLocalRing.residue ↥A ⟨y, hy⟩ := by subst h; rfl

theorem chart_residue_congr (C : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) {x y : ↥(modularFunctionFieldBar (1 * p))} (hx : x ∈ C.integers) (hy : y ∈ C.integers)
    (h : x = y) : C.residue ⟨x, hx⟩ = C.residue ⟨y, hy⟩ := by subst h; rfl

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] in

theorem ratCast_mem_of_padicValRat_nonneg (hA : A.LiesOverPrime p) (q : ℚ)
    (hq : q = 0 ∨ 0 ≤ padicValRat p q) : ((q : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by
  rcases hq with rfl | hq
  · push_cast; exact zero_mem A
  by_cases hq0 : q = 0
  · subst hq0; push_cast; exact zero_mem A
  have hp : p.Prime := Fact.out
  have hAp : A.valuation ((p : ℕ) : (AlgebraicClosure ℚ)) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq0).mpr hq

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] in

theorem residue_natCast' (hA : A.LiesOverPrime p) (m : ℕ) (h : (((m : ℚ) : ℚ) : (AlgebraicClosure ℚ)) ∈ A) :
    IsLocalRing.residue ↥A ⟨(((m : ℚ) : ℚ) : (AlgebraicClosure ℚ)), h⟩ = (m : (IsLocalRing.ResidueField ↥A)) := by
  have : (⟨(((m : ℚ) : ℚ) : (AlgebraicClosure ℚ)), h⟩ : ↥A) = ((m : ℕ) : ↥A) := Subtype.ext (by push_cast; rfl)
  rw [this, map_natCast]

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] in

theorem residue_eq_zero_of_padicValRat_pos (hA : A.LiesOverPrime p) (q : ℚ)
    (hq : q = 0 ∨ 1 ≤ padicValRat p q) (h : ((q : ℚ) : (AlgebraicClosure ℚ)) ∈ A) :
    IsLocalRing.residue ↥A ⟨((q : ℚ) : (AlgebraicClosure ℚ)), h⟩ = 0 := by
  rcases hq with rfl | hq
  · have : (⟨((0 : ℚ) : (AlgebraicClosure ℚ)), h⟩ : ↥A) = 0 := Subtype.ext (by push_cast; rfl)
    rw [this, map_zero]
  by_cases hq0 : q = 0
  · subst hq0
    have : (⟨((0 : ℚ) : (AlgebraicClosure ℚ)), h⟩ : ↥A) = 0 := Subtype.ext (by push_cast; rfl)
    rw [this, map_zero]
  have hq' : ((q : ℚ) : (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) q := (eq_ratCast _ q).symm
  have key : ∀ (x : (AlgebraicClosure ℚ)) (hx : x ∈ A), x = algebraMap ℚ (AlgebraicClosure ℚ) q → IsLocalRing.residue ↥A ⟨x, hx⟩ = 0 := by
    intro x hx hxe; subst hxe
    exact residue_algebraMap_rat_eq_zero_of_padicValRat_pos' p A hA q hq0 hq hx
  exact key _ h hq'

theorem padicValRat_sum_ge {ι : Type*} (s : Finset ι) (f : ι → ℚ) (n : ℤ)
    (h : ∀ i ∈ s, f i = 0 ∨ n ≤ padicValRat p (f i)) : (∑ i ∈ s, f i) = 0 ∨ n ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have iha := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hfa := h a (Finset.mem_insert_self a s)
    by_cases h0 : f a + ∑ i ∈ s, f i = 0
    · left; exact h0
    right
    rcases hfa with hfa | hfa
    · rw [hfa, zero_add] at h0 ⊢
      rcases iha with h1 | h1
      · exact absurd h1 h0
      · exact h1
    rcases iha with h1 | h1
    · rw [h1, add_zero]; exact hfa
    · exact (le_min hfa h1).trans (padicValRat.min_le_padicValRat_add h0)

end Combo
section Bifilt

variable (p : ℕ) [Fact p.Prime]

def VS (m : ℤ) (x : ℚ) : Prop := m ≤ padicValRat p x ∨ x = 0

variable {p}

theorem vs_zero (m : ℤ) : VS p m 0 := Or.inr rfl

theorem vs_one {m : ℤ} (hm : m ≤ 0) : VS p m 1 := Or.inl (by rw [padicValRat.one]; exact hm)

theorem vs_mono {m m' : ℤ} (h : m' ≤ m) {x : ℚ} (hx : VS p m x) : VS p m' x := by
  rcases hx with hx | hx
  · exact Or.inl (h.trans hx)
  · exact Or.inr hx

theorem vs_neg {m : ℤ} {x : ℚ} (hx : VS p m x) : VS p m (-x) := by
  rcases hx with hx | hx
  · exact Or.inl (by rwa [padicValRat.neg])
  · exact Or.inr (by rw [hx, neg_zero])

theorem vs_mul {m m' : ℤ} {x y : ℚ} (hx : VS p m x) (hy : VS p m' y) : VS p (m + m') (x * y) := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · by_cases hx0 : x = 0
      · exact Or.inr (by rw [hx0, zero_mul])
      by_cases hy0 : y = 0
      · exact Or.inr (by rw [hy0, mul_zero])
      exact Or.inl (by rw [padicValRat.mul hx0 hy0]; exact add_le_add hx hy)
    · exact Or.inr (by rw [hy, mul_zero])
  · exact Or.inr (by rw [hx, zero_mul])

theorem vs_add {m : ℤ} {x y : ℚ} (hx : VS p m x) (hy : VS p m y) : VS p m (x + y) := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · by_cases hxy : x + y = 0
      · exact Or.inr hxy
      · exact Or.inl ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))
    · rw [hy, add_zero]; exact Or.inl hx
  · rw [hx, zero_add]; exact hy

theorem vs_sub {m : ℤ} {x y : ℚ} (hx : VS p m x) (hy : VS p m y) : VS p m (x - y) := by
  rw [sub_eq_add_neg]; exact vs_add hx (vs_neg hy)

variable {r : ℕ} {u₀ T z : Fin r} {a : Fin r → ℚ} {b : ℚ}

theorem matU_bifiltered (p : ℕ) [Fact p.Prime] (n : Fin r → ℕ)
    (hnu : n u₀ = 1) (hnT : n T = 2) (hnz : n z = 0)
    (huT : u₀ ≠ T) (huz : u₀ ≠ z) (hTz : T ≠ z) (hau : a u₀ = 1)
    (ha : ∀ j, max 0 ((n u₀ : ℤ) - (n j : ℤ)) ≤ padicValRat p (a j) ∨ a j = 0)
    (hb : (2 : ℤ) ≤ padicValRat p b ∨ b = 0) :
    ∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (matU u₀ T z a b i j) ∨ matU u₀ T z a b i j = 0 := by
  intro i j
  show VS p _ _
  by_cases hiu : i = u₀
  · subst hiu
    rw [matU_apply_u0]
    exact ha j
  by_cases hiT : i = T
  · subst hiT
    rw [matU_apply_T (Ne.symm huT)]
    simp only [rowB]
    by_cases hjT : j = i
    · subst hjT
      rw [if_pos rfl]
      exact vs_one (by simp)
    rw [if_neg hjT]
    by_cases hjz : j = z
    · subst hjz
      rw [if_pos rfl, hnT, hnz]
      exact hb
    · rw [if_neg hjz]
      exact vs_zero _
  · rw [matU_apply_other hiu hiT]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact vs_one (by simp)
    · rw [if_neg hij]
      exact vs_zero _

theorem matV_bifiltered (p : ℕ) [Fact p.Prime] (n : Fin r → ℕ)
    (hnu : n u₀ = 1) (hnT : n T = 2) (hnz : n z = 0)
    (huT : u₀ ≠ T) (huz : u₀ ≠ z) (hTz : T ≠ z) (hau : a u₀ = 1)
    (ha : ∀ j, max 0 ((n u₀ : ℤ) - (n j : ℤ)) ≤ padicValRat p (a j) ∨ a j = 0)
    (hb : (2 : ℤ) ≤ padicValRat p b ∨ b = 0) :
    ∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (matV u₀ T z a b i j) ∨ matV u₀ T z a b i j = 0 := by
  have ha' : ∀ j, VS p (max 0 ((n u₀ : ℤ) - (n j : ℤ))) (a j) := ha
  have hb' : VS p 2 b := hb
  intro i j
  show VS p _ _
  by_cases hiu : i = u₀
  · subst hiu
    rw [matV_apply_u0]
    by_cases hju : j = i
    · subst hju
      rw [if_pos rfl, if_neg huz, hau]
      norm_num
      exact vs_one (by simp)
    rw [if_neg hju]
    by_cases hjz : j = z
    · subst hjz
      rw [if_pos rfl, hnu, hnz]

      have h1 : VS p 1 (a j) := by have := ha' j; rwa [hnu, hnz] at this
      have h2 : VS p 1 (a T * b) := by
        have hT0 : VS p 0 (a T) := by have := ha' T; rw [hnu, hnT] at this; simpa using this
        exact vs_mono (by norm_num) (vs_mul hT0 hb')
      simpa using vs_add (vs_sub (vs_zero 1) h1) h2
    · rw [if_neg hjz, add_zero]
      have h1 : VS p (max 0 ((n i : ℤ) - (n j : ℤ))) (a j) := ha' j
      exact vs_sub (vs_zero _) h1
  by_cases hiT : i = T
  · subst hiT
    rw [matV_apply_T (Ne.symm huT)]
    simp only [rowB]
    by_cases hjT : j = i
    · subst hjT
      rw [if_pos rfl, if_pos rfl]
      norm_num
      exact vs_one (by simp)
    rw [if_neg hjT, if_neg hjT]
    by_cases hjz : j = z
    · subst hjz
      rw [if_pos rfl, hnT, hnz]
      simpa using vs_sub (vs_zero 2) hb'
    · rw [if_neg hjz, sub_zero]
      exact vs_zero _
  · rw [matV_apply_other hiu hiT]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact vs_one (by simp)
    · rw [if_neg hij]
      exact vs_zero _

end Bifilt

section Main

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)

open P2MF2J

include hA in

theorem zeroChart_residue_goodFamilyZero_zero (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (l : Fin r) (hl : (l : ℕ) = 0) : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ = 1 := by
  have hg : goodFamilyZero Φ.toFamData l = 1 := by
    unfold goodFamilyZero
    rw [hasseExp_zero p Φ l hl, pow_zero, map_one, inv_one, one_mul (Φ.t l)]
    exact Φ.t_zero l hl
  have : (⟨goodFamilyZero Φ.toFamData l, hint l⟩ : ↥(zeroChart Γ).integers) = 1 := Subtype.ext hg
  rw [this, map_one]

theorem coeffMap_frobenius_smul (c : (IsLocalRing.ResidueField ↥A)) (x : LaurentSeries (IsLocalRing.ResidueField ↥A)) :
    coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p) (c • x) = c ^ p • coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p) x := by
  rw [← HahnSeries.single_zero_mul_eq_smul, ← HahnSeries.single_zero_mul_eq_smul, map_mul, coeffMap_single, frobenius_def]

theorem coe_smul_modC (c : (IsLocalRing.ResidueField ↥A)) (y : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : ((c • y : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = c • (y : LaurentSeries (IsLocalRing.ResidueField ↥A)) := by
  rw [Algebra.smul_def,
    show ((algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) c * y : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A)) c * (y : LaurentSeries (IsLocalRing.ResidueField ↥A)) from rfl,
    algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]

theorem coe_sum_smul_modC {ι : Type*} (s : Finset ι) (c : ι → (IsLocalRing.ResidueField ↥A)) (y : ι → ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
    ((∑ i ∈ s, c i • y i : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = ∑ i ∈ s, c i • (y i : LaurentSeries (IsLocalRing.ResidueField ↥A)) := by
  show (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val (∑ i ∈ s, c i • y i) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => coe_smul_modC (A := A) (c i) (y i))

end Main

section MainThm

open P2MF2J

set_option maxHeartbeats 64000000 in

theorem twoMembers_certificate (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (he : ssValue Γ e = 0) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (D' : FamData p r)
      (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers) (l₁ l₂ : Fin r),
      IsUnit U ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
        ∨ U i j = 0) ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
        ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      1 ≤ (l₁ : ℕ) ∧ 1 ≤ (l₂ : ℕ) ∧
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l₁, hintI' l₁⟩) = 1 ∧
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l₂, hintI' l₂⟩) = 1 ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩) = 0 ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l₂, hint' l₂⟩) ≤ 0 ∧
      hasseExp D' l₁ < hasseExp D' l₂ ∧
      ∀ Q ∈ (zeroChart Γ).dom,
        ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩)
          ≠ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩) := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  have hp5 : 5 ≤ p := by omega
  have hprime : p.Prime := Fact.out

  have hn_le2 : ∀ l, hasseExp Φ.toFamData l ≤ 2 := hasseExp_le_two_of_thirteen_le p hp13 A hA Γ Δ Φ
  have hn_ge1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := one_le_hasseExp p A hA Γ Φ
  have hn_z : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp Φ.toFamData l = 0 := hasseExp_zero p Φ

  have he_wide : jWidth (ssValue Γ e) ≠ 1 := by rw [he, jWidth_of_eq_zero rfl]; decide
  have hnode0 : nodeSrc Γ e = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (0 : (IsLocalRing.ResidueField ↥A)) := by
    show charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p) = _
    rw [he, zero_pow hprime.ne_zero]
  have h0node : charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (0 : (IsLocalRing.ResidueField ↥A)) ∈ (zeroChart Γ).nodes := by
    rw [mem_zeroChart_nodes_iff]
    exact ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, by rw [he, zero_pow hprime.ne_zero]⟩
  have hN : 0 < (wOne Γ).card := Finset.card_pos.mpr (wOne_nonempty Γ hp13)

  have hV2 := mem_span_zeroChart_residue_hasseExp_le_one_of_forall_ord_nodeSrc_ge p hp5 A hA Γ Δ Φ hint hLI
    (hfun Γ) (hfun_hreg Γ) (hfun_hnode Γ)
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun (IsLocalRing.ResidueField ↥A)).mp hV2

  have hlamp : ∀ i, lam i ^ p = lam i := by
    let f : {l : Fin r // hasseExp Φ.toFamData l ≤ 1} → LaurentSeries (IsLocalRing.ResidueField ↥A) := fun i => (((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A))
    have hsubLI := hLI.comp (Subtype.val : {l : Fin r // hasseExp Φ.toFamData l ≤ 1} → Fin r) Subtype.val_injective
    have hfLI : LinearIndependent (IsLocalRing.ResidueField ↥A) f := by
      rw [linearIndependent_iff']
      intro s g hg i hi
      have hcoe : ((∑ j ∈ s, g j • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j.1, hint j.1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = ∑ j ∈ s, g j • f j :=
        coe_sum_smul_modC (A := A) s g _
      have h0 : (∑ j ∈ s, g j • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j.1, hint j.1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 0 := by
        apply Subtype.ext
        rw [hcoe]; exact hg
      exact linearIndependent_iff'.mp hsubLI s g h0 i hi
    have hfix : ∀ i, (coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p)).toAddMonoidHom (f i) = f i := fun i =>
      ModularCurve.MultCovering.coeffMap_frobenius_zeroChart_residue_goodFamilyZero p A hA Γ Φ hint i.1
    have hsum : (((∑ i, lam i • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = ∑ i, lam i • f i :=
      coe_sum_smul_modC (A := A) Finset.univ lam _
    have hh : (coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p)).toAddMonoidHom (∑ i, lam i • f i) = ∑ i, lam i • f i := by
      rw [← hsum, hlam]
      exact coeffMap_frobenius_hfun Γ
    exact pow_eq_self_of_semilinear_fixed p (coeffMap (frobenius (IsLocalRing.ResidueField ↥A) p)).toAddMonoidHom
      (fun c x => coeffMap_frobenius_smul p A c x) f hfLI hfix lam hh

  obtain ⟨b₁, hb₁⟩ := wOne_nonempty Γ hp13
  have hex_u : ∃ u : {l : Fin r // hasseExp Φ.toFamData l ≤ 1}, 1 ≤ ((u.1 : Fin r) : ℕ) ∧ lam u ≠ 0 := by
    by_contra hno
    push_neg at hno

    have hord := ord_pt_hfun_of_mem Γ hb₁
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have : hfun Γ = 0 := by rw [← hlam]; simp
      rw [this, Place.ord_zero] at hord; exact absurd hord (by norm_num)
    let z₀ : Fin r := ⟨0, hr⟩
    have hz₀ : hasseExp Φ.toFamData z₀ ≤ 1 := by rw [hn_z z₀ rfl]; exact Nat.zero_le _
    let i₀ : {l : Fin r // hasseExp Φ.toFamData l ≤ 1} := ⟨z₀, hz₀⟩
    have hsingle : ∑ i, lam i • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩ = lam i₀ • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData z₀, hint z₀⟩ := by
      apply Finset.sum_eq_single i₀
      · intro i _ hi
        have hi1 : 1 ≤ ((i.1 : Fin r) : ℕ) := by
          by_contra h0
          push_neg at h0
          apply hi
          apply Subtype.ext
          apply Fin.ext
          show ((i.1 : Fin r) : ℕ) = 0
          omega
        rw [hno i hi1, zero_smul]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [zeroChart_residue_goodFamilyZero_zero p A hA Γ Φ hint z₀ rfl] at hsingle
    have hconst : hfun Γ = algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (lam i₀) := by rw [← hlam, hsingle, Algebra.algebraMap_eq_smul_one]
    rw [hconst, Place.ord_algebraMap] at hord
    exact absurd hord (by norm_num)
  obtain ⟨u₀, hu₀1, hlamu₀⟩ := hex_u
  have hnu₀ : hasseExp Φ.toFamData u₀.1 = 1 := le_antisymm u₀.2 (hn_ge1 u₀.1 hu₀1)

  have hlamp' : ∀ i, (lam i * (lam u₀)⁻¹) ^ p = lam i * (lam u₀)⁻¹ := fun i => by
    rw [mul_pow, inv_pow, hlamp i, hlamp u₀]
  have hlift : ∀ i, ∃ m : ℕ, m < p ∧ (m : (IsLocalRing.ResidueField ↥A)) = lam i * (lam u₀)⁻¹ :=
    fun i => exists_natCast_eq_of_pow_eq_self p (hlamp' i)
  choose mN hmNlt hmN using hlift

  obtain ⟨liftN, hliftN_u₀, hliftN_val, hliftN_out⟩ : ∃ L : Fin r → ℕ, L u₀.1 = 1 ∧
      (∀ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1}, ((L i.1 : ℕ) : (IsLocalRing.ResidueField ↥A)) = lam i * (lam u₀)⁻¹) ∧
      (∀ j, ¬ hasseExp Φ.toFamData j ≤ 1 → L j = 0) := by
    refine ⟨fun j => if h : hasseExp Φ.toFamData j ≤ 1 then (if j = u₀.1 then 1 else mN ⟨j, h⟩) else 0, ?_, ?_, ?_⟩
    · simp [u₀.2]
    · intro i
      by_cases hi : (i.1 : Fin r) = u₀.1
      · rw [show i = u₀ from Subtype.ext hi]
        simp [u₀.2, mul_inv_cancel₀ hlamu₀]
      · simp only [dif_pos i.2, if_neg hi]
        exact hmN i
    · intro j hj; simp [hj]

  obtain ⟨hintI, hres0, P, hP, hPli, hPspan⟩ := Φ.t_inf A hA Γ
  obtain ⟨cT, hcT2, hcTsum⟩ := exists_combination_hasseExp_two_eq_prod_widthOne p hp13 A hA Γ Δ Φ hint hLI
    ⟨e, he_wide⟩ hintI P hP hPli
  have hev : ∑ l, cT l * (P l).eval 0 = ∏ e' ∈ Finset.univ.filter (fun e' => jWidth (ssValue Γ e') = 1),
      (0 - ssValue Γ e') := by
    have h := congrArg (Polynomial.eval 0) hcTsum
    rw [Polynomial.eval_finset_sum, Polynomial.eval_prod] at h
    simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    exact h
  have hev_ne : ∑ l, cT l * (P l).eval 0 ≠ 0 := by
    rw [hev, Finset.prod_ne_zero_iff]
    intro e' he'
    rw [Finset.mem_filter] at he'
    rw [zero_sub, neg_ne_zero]
    intro h0
    rw [h0, jWidth_of_eq_zero rfl] at he'
    exact absurd he'.2 (by decide)
  obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hev_ne
  have hcT0 : cT T ≠ 0 := left_ne_zero_of_mul hT
  have hPT0 : (P T).eval 0 ≠ 0 := right_ne_zero_of_mul hT
  have hnT : hasseExp Φ.toFamData T = 2 := hcT2 T hcT0
  have hT1 : 1 ≤ (T : ℕ) := by
    by_contra h; push_neg at h
    have := hn_z T (by omega); omega
  have huT : (u₀.1 : Fin r) ≠ T := by intro h; rw [h] at hnu₀; omega

  have hr : 0 < r := Fin.pos T
  obtain ⟨z, hz⟩ : ∃ z : Fin r, (z : ℕ) = 0 := ⟨⟨0, hr⟩, rfl⟩
  have hnz : hasseExp Φ.toFamData z = 0 := hn_z z hz
  have huz : (u₀.1 : Fin r) ≠ z := by intro h; rw [h] at hnu₀; omega
  have hTz : T ≠ z := by intro h; rw [h] at hnT; omega

  obtain ⟨ν, hν1, hνgood⟩ : ∃ ν : ℕ, ν ≤ 1 ∧
      (∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData j ≤ 1 then ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) * (P j).eval 0 else 0))
        + (ν : (IsLocalRing.ResidueField ↥A)) * (P T).eval 0 ≠ 0 := by
    by_cases hS : (∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData j ≤ 1 then ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) * (P j).eval 0 else 0)) = 0
    · exact ⟨1, le_rfl, by rw [hS, zero_add, Nat.cast_one, one_mul]; exact hPT0⟩
    · exact ⟨0, Nat.zero_le _, by rw [Nat.cast_zero, zero_mul, add_zero]; exact hS⟩

  obtain ⟨cN, hcN1, hcNgood⟩ : ∃ cN : ℕ, cN ≤ 1 ∧
      ((nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩) < 0 ∨
        (0 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩) ∧ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩) + (cN : (IsLocalRing.ResidueField ↥A)) ≠ 0)) := by
    by_cases hpole : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩) < 0
    · exact ⟨0, Nat.zero_le _, Or.inl hpole⟩
    push_neg at hpole
    by_cases hval : (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩) = 0
    · exact ⟨1, le_rfl, Or.inr ⟨hpole, by rw [hval, zero_add, Nat.cast_one]; exact one_ne_zero⟩⟩
    · exact ⟨0, Nat.zero_le _, Or.inr ⟨hpole, by rw [Nat.cast_zero, add_zero]; exact hval⟩⟩

  let aRow : Fin r → ℚ := fun j => if j = T then (ν : ℚ)
    else if hasseExp Φ.toFamData j ≤ 1 then (p : ℚ) ^ (1 - hasseExp Φ.toFamData j) * (liftN j : ℚ) else 0
  let bEnt : ℚ := (p : ℚ) ^ 2 * (cN : ℚ)
  have haRow_T : aRow T = (ν : ℚ) := by simp [aRow]
  have haRow_le : ∀ j, j ≠ T → hasseExp Φ.toFamData j ≤ 1 →
      aRow j = (p : ℚ) ^ (1 - hasseExp Φ.toFamData j) * (liftN j : ℚ) := by
    intro j hjT hj; simp [aRow, hjT, hj]
  have haRow_out : ∀ j, j ≠ T → ¬ hasseExp Φ.toFamData j ≤ 1 → aRow j = 0 := by
    intro j hjT hj; simp [aRow, hjT, hj]
  have haRow_u₀ : aRow u₀.1 = 1 := by
    rw [haRow_le u₀.1 huT u₀.2, hnu₀, hliftN_u₀]; simp
  let U : Matrix (Fin r) (Fin r) ℚ := matU u₀.1 T z aRow bEnt
  have hUV := matU_mul_matV (u₀ := u₀.1) (T := T) (z := z) (a := aRow) (b := bEnt) huT huz hTz haRow_u₀
  have hUunit : IsUnit U := isUnit_matU huT huz hTz haRow_u₀
  have hUinv : U⁻¹ = matV u₀.1 T z aRow bEnt := matU_inv huT huz hTz haRow_u₀
  have hUu : ∀ j, U u₀.1 j = aRow j := fun j => matU_apply_u0 j
  have hUT : ∀ j, U T j = rowB T z bEnt j := fun j => matU_apply_T (Ne.symm huT) j

  let tRat' : Fin r → ↥(modularFunctionFieldFull (1 * p)) := fun i => ∑ j, U i j • Φ.toFamData.tRat j
  let D' : FamData p r :=
    ⟨fun i => ⟨coeffEmb (AlgebraicClosure ℚ) ((tRat' i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (tRat' i).2⟩, tRat', fun i => rfl⟩
  have htRat : ∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j := fun i => rfl
  have hcoe_t : ∀ j (m : ℤ), ((Φ.t j : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)).coeff m
      = algebraMap ℚ (AlgebraicClosure ℚ) (((Φ.toFamData.tRat j : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m) := by
    intro j m
    have := congrArg (fun x : ↥(modularFunctionFieldBar (1 * p)) => ((x : LaurentSeries (AlgebraicClosure ℚ))).coeff m) (Φ.toFamData.t_eq j)
    simpa only [coeffEmb_coeff] using this
  have ht : ∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j := by
    intro i
    apply Subtype.ext
    show coeffEmb (AlgebraicClosure ℚ) ((tRat' i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)
      = (((∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j : ↥(modularFunctionFieldBar (1 * p)))) : LaurentSeries (AlgebraicClosure ℚ))
    have hr : (((∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j : ↥(modularFunctionFieldBar (1 * p)))) : LaurentSeries (AlgebraicClosure ℚ))
        = ∑ j, algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * ((Φ.t j : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      show (modularFunctionFieldBar (1 * p)).val (∑ j, _) = _
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_mul]; rfl)
    rw [hr]
    ext m
    rw [coeffEmb_coeff, coe_sum_smul_coeff, map_sum, HahnSeries.coeff_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
      map_mul, hcoe_t]

  have hzcoeff : ∀ i (m : ℤ), (zeroSeries D' i).coeff m = ∑ j, U i j * (zeroSeries Φ.toFamData j).coeff m := by
    intro i m
    show (((frickeInvolutionFull (1 * p) (tRat' i) : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m = _
    have : frickeInvolutionFull (1 * p) (tRat' i) = ∑ j, U i j • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat j) := by
      show frickeInvolutionFull (1 * p) (∑ j, U i j • Φ.toFamData.tRat j) = _
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def])
    rw [this, coe_sum_smul_coeff]
    rfl

  have hUother : ∀ i, i ≠ u₀.1 → i ≠ T → ∀ j, U i j = if i = j then 1 else 0 :=
    fun i hiu hiT j => matU_apply_other hiu hiT j
  have hz_other : ∀ i, i ≠ u₀.1 → i ≠ T → zeroSeries D' i = zeroSeries Φ.toFamData i := by
    intro i hiu hiT
    ext m
    rw [hzcoeff, Finset.sum_eq_single i (fun j _ hj => by rw [hUother i hiu hiT, if_neg (Ne.symm hj), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), hUother i hiu hiT, if_pos rfl, one_mul]
  have ht_other : ∀ i, i ≠ u₀.1 → i ≠ T → D'.t i = Φ.t i := by
    intro i hiu hiT
    rw [ht, Finset.sum_eq_single i (fun j _ hj => by rw [hUother i hiu hiT, if_neg (Ne.symm hj), map_zero, map_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), hUother i hiu hiT, if_pos rfl, map_one, map_one, one_mul (Φ.t i)]

  have hcontΦ : ∀ j (m : ℤ), (zeroSeries Φ.toFamData j).coeff m ≠ 0 →
      ((hasseExp Φ.toFamData j : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries Φ.toFamData j).coeff m) := by
    intro j m hm
    have hc := (isContent_hasseContent Φ.toFamData j (exists_isContent_goodFamily p A hA Φ j)).1 m hm
    rwa [← hasseExp_eq_hasseContent p A hA Γ Φ j] at hc

  have hp1 : (1 : ℤ) ≤ 1 := le_rfl
  have hvp : padicValRat p (p : ℚ) = 1 := padicValRat.self hprime.one_lt
  have hvnat : ∀ m : ℕ, m ≠ 0 → 0 ≤ padicValRat p (m : ℚ) := by
    intro m hm; rw [padicValRat.of_nat]; exact_mod_cast Nat.zero_le _
  have hvpow : ∀ k : ℕ, padicValRat p ((p : ℚ) ^ k) = k := by
    intro k; rw [padicValRat.pow _, hvp, mul_one]
  have haRow_val : ∀ j, aRow j = 0 ∨
      (0 ≤ padicValRat p (aRow j) ∧ ((1 : ℤ) - hasseExp Φ.toFamData j) ≤ padicValRat p (aRow j)) := by
    intro j
    by_cases hjT : j = T
    · subst hjT
      rw [haRow_T]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hν1 with h | h
      · left; simp [h]
      · right; rw [h, hnT]; simp
    by_cases hj : hasseExp Φ.toFamData j ≤ 1
    · rw [haRow_le j hjT hj]
      by_cases hL : liftN j = 0
      · left; simp [hL]
      · right
        rw [padicValRat.mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr hprime.ne_zero)) (Nat.cast_ne_zero.mpr hL), hvpow]
        have := hvnat (liftN j) hL
        have hcast : (((1 - hasseExp Φ.toFamData j : ℕ)) : ℤ) = 1 - (hasseExp Φ.toFamData j : ℤ) := by
          push_cast [Nat.cast_sub hj]; ring
        rw [hcast]
        constructor <;> omega
    · left; exact haRow_out j hjT hj
  have hbEnt_val : bEnt = 0 ∨ (2 : ℤ) ≤ padicValRat p bEnt := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcN1 with h | h
    · left; simp [bEnt, h]
    · right; simp only [bEnt, h, Nat.cast_one, mul_one, hvpow]; norm_num

  have hlow_u : ∀ m : ℤ, (zeroSeries D' u₀.1).coeff m = 0 ∨ (1 : ℤ) ≤ padicValRat p ((zeroSeries D' u₀.1).coeff m) := by
    intro m
    rw [hzcoeff]
    apply padicValRat_sum_ge
    intro j _
    rw [hUu]
    by_cases hs : (zeroSeries Φ.toFamData j).coeff m = 0
    · left; rw [hs, mul_zero]
    rcases haRow_val j with ha | ha
    · left; rw [ha, zero_mul]
    by_cases ha0 : aRow j = 0
    · left; rw [ha0, zero_mul]
    right
    rw [padicValRat.mul ha0 hs]
    have := hcontΦ j m hs
    have := ha.2
    omega
  have hlow_T : ∀ m : ℤ, (zeroSeries D' T).coeff m = 0 ∨ (2 : ℤ) ≤ padicValRat p ((zeroSeries D' T).coeff m) := by
    intro m
    rw [hzcoeff]
    apply padicValRat_sum_ge
    intro j _
    rw [hUT]
    simp only [rowB]
    by_cases hjT : j = T
    · subst hjT
      rw [if_pos rfl, one_mul]
      by_cases hs : (zeroSeries Φ.toFamData j).coeff m = 0
      · left; exact hs
      · right; have := hcontΦ j m hs; rw [hnT] at this; exact_mod_cast this
    rw [if_neg hjT]
    by_cases hjz : j = z
    · subst hjz
      rw [if_pos rfl]
      by_cases hs : (zeroSeries Φ.toFamData j).coeff m = 0
      · left; rw [hs, mul_zero]
      rcases hbEnt_val with hb | hb
      · left; rw [hb, zero_mul]
      · right
        rw [padicValRat.mul (by intro h; rw [h] at hb; simp at hb) hs]
        have := hcontΦ j m hs
        omega
    · left; rw [if_neg hjz, zero_mul]

  have hunit : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ ≠ 0 := fun l => hLI.ne_zero l
  have hRES_z : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData z, hint z⟩ = 1 := zeroChart_residue_goodFamilyZero_zero p A hA Γ Φ hint z hz

  have hsubsum : ∀ g : Fin r → ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1), (∀ j, ¬ hasseExp Φ.toFamData j ≤ 1 → g j = 0) →
      ∑ j, g j = ∑ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1}, g i.1 := by
    intro g hg
    rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin r => hasseExp Φ.toFamData l ≤ 1) (by intro x; simp)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    apply hg
    simpa using hj
  have hlam' : ∑ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1}, (lam i * (lam u₀)⁻¹) • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩
      = (lam u₀)⁻¹ • hfun Γ := by
    rw [← hlam, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [smul_smul, mul_comm])

  let y₁ : Fin r → ℚ := fun j => if j = T then (ν : ℚ) * p else if hasseExp Φ.toFamData j ≤ 1 then (liftN j : ℚ) else 0
  have hy₁A : ∀ j, ((y₁ j : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by
    intro j
    apply ratCast_mem_of_padicValRat_nonneg hA
    by_cases hjT : j = T
    · simp only [y₁, if_pos hjT]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hν1 with h | h
      · left; simp [h]
      · right; rw [h, Nat.cast_one, one_mul, hvp]; norm_num
    · simp only [y₁, if_neg hjT]
      split_ifs with hj
      · by_cases hL : liftN j = 0
        · left; simp [hL]
        · right; exact hvnat _ hL
      · left; rfl
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hprime.ne_zero
  have hpc : algebraMap ℚ (AlgebraicClosure ℚ) (p : ℚ) = ((p : ℕ) : (AlgebraicClosure ℚ)) := map_natCast (algebraMap ℚ (AlgebraicClosure ℚ)) p
  have hscal₁ : ∀ j, (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ))))⁻¹ * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (aRow j)) * Φ.t j)
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((y₁ j : ℚ) : (AlgebraicClosure ℚ)) * goodFamilyZero Φ.toFamData j := by
    intro j
    unfold goodFamilyZero

    have hq : (p : ℚ)⁻¹ * aRow j = y₁ j * ((p : ℚ) ^ hasseExp Φ.toFamData j)⁻¹ := by
      by_cases hjT : j = T
      · subst hjT
        simp only [y₁, if_pos rfl, haRow_T, hnT]
        field_simp
      by_cases hj : hasseExp Φ.toFamData j ≤ 1
      · rw [haRow_le j hjT hj]
        simp only [y₁, if_neg hjT, if_pos hj]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with h | h
        · rw [h]; simp only [Nat.sub_zero, pow_one, pow_zero, inv_one, mul_one]; exact inv_mul_cancel_left₀ hpq _
        · rw [h]; simp only [Nat.sub_self, pow_zero, one_mul, pow_one]; ring
      · rw [haRow_out j hjT hj]
        simp only [y₁, if_neg hjT, if_neg hj]
        simp
    have hq' := congrArg (fun x : ℚ => algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) x)) hq
    simp only [map_mul, map_inv₀, map_pow (algebraMap ℚ (AlgebraicClosure ℚ))] at hq'
    rw [hpc, eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ)) (y₁ j)] at hq'
    rw [← mul_assoc, ← mul_assoc]
    exact congrArg (· * Φ.t j) hq'
  have hrow₁ : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ))))⁻¹ * D'.t u₀.1
      = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((y₁ j : ℚ) : (AlgebraicClosure ℚ)) * goodFamilyZero Φ.toFamData j := by
    rw [ht, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [hUu]; exact hscal₁ j)
  obtain ⟨hmem₁, hres₁⟩ := chart_residue_sum (zeroChart Γ) (fun j => goodFamilyZero Φ.toFamData j) hint
    (fun j => ((y₁ j : ℚ) : (AlgebraicClosure ℚ))) hy₁A
  have hres₁' : (zeroChart Γ).residue ⟨_, hmem₁⟩ = (lam u₀)⁻¹ • hfun Γ := by
    rw [hres₁, ← hlam']
    rw [hsubsum _ (fun j hj => by
      have hjT : j ≠ T ∨ j = T := (em (j = T)).symm
      by_cases hjT : j = T
      · subst hjT
        have : IsLocalRing.residue ↥A ⟨((y₁ j : ℚ) : (AlgebraicClosure ℚ)), hy₁A j⟩ = 0 := by
          apply residue_eq_zero_of_padicValRat_pos hA
          simp only [y₁, if_pos rfl]
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hν1 with h | h
          · left; simp [h]
          · right; rw [h, Nat.cast_one, one_mul, hvp]
        rw [this, zero_smul]
      · have : IsLocalRing.residue ↥A ⟨((y₁ j : ℚ) : (AlgebraicClosure ℚ)), hy₁A j⟩ = 0 := by
          have h0 : y₁ j = 0 := by simp [y₁, hjT, hj]
          apply residue_eq_zero_of_padicValRat_pos hA; left; exact h0
        rw [this, zero_smul])]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hiT : (i.1 : Fin r) ≠ T := by intro h; have := i.2; rw [h, hnT] at this; omega
    congr 1
    have h1 : y₁ i.1 = (liftN i.1 : ℚ) := by simp [y₁, hiT, i.2]
    have : IsLocalRing.residue ↥A ⟨((y₁ i.1 : ℚ) : (AlgebraicClosure ℚ)), hy₁A i.1⟩ = ((liftN i.1 : ℕ) : (IsLocalRing.ResidueField ↥A)) := by
      have hm : ((((liftN i.1 : ℕ) : ℚ) : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by have := hy₁A i.1; rwa [h1] at this
      rw [← residue_natCast' hA (liftN i.1) hm]
      congr 1; apply Subtype.ext; push_cast [h1]; rfl
    rw [this, hliftN_val i]

  let y₂ : Fin r → ℚ := fun j => if j = T then 1 else if j = z then (cN : ℚ) else 0
  have hy₂A : ∀ j, ((y₂ j : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by
    intro j
    apply ratCast_mem_of_padicValRat_nonneg hA
    simp only [y₂]
    split_ifs with h1 h2
    · right; rw [padicValRat.one]
    · by_cases hc : cN = 0
      · left; simp [hc]
      · right; exact hvnat _ hc
    · left; rfl
  have hrow₂ : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ 2))⁻¹ * D'.t T
      = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((y₂ j : ℚ) : (AlgebraicClosure ℚ)) * goodFamilyZero Φ.toFamData j := by
    rw [ht, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hUT]
    unfold goodFamilyZero
    have hq : ((p : ℚ) ^ 2)⁻¹ * rowB T z bEnt j = y₂ j * ((p : ℚ) ^ hasseExp Φ.toFamData j)⁻¹ := by
      simp only [rowB, y₂]
      by_cases hjT : j = T
      · subst hjT; simp only [if_pos rfl, if_true, hnT, mul_one, one_mul]
      rw [if_neg hjT, if_neg hjT]
      by_cases hjz : j = z
      · subst hjz; simp only [if_pos rfl, if_true, hnz, bEnt, pow_zero, inv_one, mul_one]; exact inv_mul_cancel_left₀ (pow_ne_zero _ hpq) _
      · rw [if_neg hjz, if_neg hjz]; simp
    have hq' := congrArg (fun x : ℚ => algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) x)) hq
    simp only [map_mul, map_inv₀, map_pow (algebraMap ℚ (AlgebraicClosure ℚ))] at hq'
    rw [hpc, eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ)) (y₂ j)] at hq'
    rw [← mul_assoc, ← mul_assoc]
    exact congrArg (· * Φ.t j) hq'
  obtain ⟨hmem₂, hres₂⟩ := chart_residue_sum (zeroChart Γ) (fun j => goodFamilyZero Φ.toFamData j) hint
    (fun j => ((y₂ j : ℚ) : (AlgebraicClosure ℚ))) hy₂A
  have hres₂' : (zeroChart Γ).residue ⟨_, hmem₂⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩ + algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (cN : (IsLocalRing.ResidueField ↥A)) := by
    rw [hres₂, Fintype.sum_eq_add T z hTz (fun j hj => by
      have : IsLocalRing.residue ↥A ⟨((y₂ j : ℚ) : (AlgebraicClosure ℚ)), hy₂A j⟩ = 0 := by
        apply residue_eq_zero_of_padicValRat_pos hA; left; simp [y₂, hj.1, hj.2]
      rw [this, zero_smul])]
    have e1 : IsLocalRing.residue ↥A ⟨((y₂ T : ℚ) : (AlgebraicClosure ℚ)), hy₂A T⟩ = 1 := by
      have h1 : y₂ T = ((1 : ℕ) : ℚ) := by simp [y₂]
      have hm : ((((1 : ℕ) : ℚ) : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by have := hy₂A T; rwa [h1] at this
      rw [show (⟨((y₂ T : ℚ) : (AlgebraicClosure ℚ)), hy₂A T⟩ : ↥A) = ⟨_, hm⟩ from Subtype.ext (by push_cast [h1]; rfl),
        residue_natCast' hA 1 hm, Nat.cast_one]
    have e2 : IsLocalRing.residue ↥A ⟨((y₂ z : ℚ) : (AlgebraicClosure ℚ)), hy₂A z⟩ = (cN : (IsLocalRing.ResidueField ↥A)) := by
      have h1 : y₂ z = ((cN : ℕ) : ℚ) := by simp [y₂, hTz.symm]
      have hm : ((((cN : ℕ) : ℚ) : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by have := hy₂A z; rwa [h1] at this
      rw [show (⟨((y₂ z : ℚ) : (AlgebraicClosure ℚ)), hy₂A z⟩ : ↥A) = ⟨_, hm⟩ from Subtype.ext (by push_cast [h1]; rfl),
        residue_natCast' hA cN hm]
    rw [e1, e2, one_smul, hRES_z, Algebra.algebraMap_eq_smul_one]

  have hpA : ((p : ℕ) : (AlgebraicClosure ℚ)) ∈ A := natCast_mem A p
  have hres_p : IsLocalRing.residue ↥A ⟨(p : (AlgebraicClosure ℚ)), hpA⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA

  have hupper : ∀ (i : Fin r) (N : ℕ), (∀ m : ℤ, (zeroSeries D' i).coeff m = 0 ∨ ((N : ℤ) + 1) ≤ padicValRat p ((zeroSeries D' i).coeff m)) →
      ∀ (hm : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ N))⁻¹ * D'.t i ∈ (zeroChart Γ).integers),
        (zeroChart Γ).residue ⟨_, hm⟩ = 0 := by
    intro i N hall hm

    have hf₂ : frickeInvolutionBar (1 * p) (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ (N + 1))⁻¹)) * D'.t i)
        ∈ (infChart Γ).integers := by
      apply mem_infChart_integers_of_forall_coeff_mem Γ
      intro m
      rw [coe_frickeInvolutionBar_algebraMap_mul D' i, coeffEmb_coeff]
      rw [show ((((p : ℚ) ^ (N + 1))⁻¹ • zeroSeries D' i).coeff m) = ((p : ℚ) ^ (N + 1))⁻¹ * (zeroSeries D' i).coeff m from rfl,
        eq_ratCast]
      apply ratCast_mem_of_padicValRat_nonneg hA
      rcases hall m with h0 | h0
      · left; rw [h0, mul_zero]
      · right
        have hne : (zeroSeries D' i).coeff m ≠ 0 := by intro h; rw [h] at h0; simp at h0; omega
        rw [padicValRat.mul (inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr hprime.ne_zero))) hne,
          padicValRat.inv, hvpow]
        push_cast; omega
    have hf₂' : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ (N + 1))⁻¹)) * D'.t i ∈ (zeroChart Γ).integers := hf₂

    have hsplit : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ N))⁻¹ * D'.t i
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ (N + 1))⁻¹)) * D'.t i) := by
      rw [← mul_assoc, ← map_inv₀, ← map_mul]
      congr 1
      have hy : algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ (N + 1))⁻¹) = ((p : (AlgebraicClosure ℚ)) ^ (N + 1))⁻¹ := by
        rw [map_inv₀, map_pow, map_natCast]
      rw [hy]
      have hp0 : ((p : (AlgebraicClosure ℚ))) ≠ 0 := by exact_mod_cast hprime.ne_zero
      rw [pow_succ, mul_inv, mul_comm ((p : (AlgebraicClosure ℚ)) ^ N)⁻¹, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul ((p : (AlgebraicClosure ℚ)) ^ N)⁻¹]
    have hpint : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) ∈ (zeroChart Γ).integers := ((zeroChart Γ).algebraMap_mem_iff _).mpr hpA
    have heq : (⟨_, hm⟩ : ↥(zeroChart Γ).integers) = ⟨_, hpint⟩ * ⟨_, hf₂'⟩ := Subtype.ext hsplit
    rw [heq, map_mul]
    have : (zeroChart Γ).residue ⟨_, hpint⟩ = 0 := by
      have := (zeroChart Γ).residue_algebraMap ⟨(p : (AlgebraicClosure ℚ)), hpA⟩
      rw [hres_p, map_zero] at this
      exact this
    rw [this, zero_mul]
  have hhfun0 : hfun Γ ≠ 0 := by
    intro h0
    have := ord_pt_hfun_of_mem Γ hb₁
    rw [h0, Place.ord_zero] at this; exact absurd this (by norm_num)
  have hcont_u : IsContent D' u₀.1 ((1 : ℕ) : ℤ) := by
    refine ⟨fun m hm => ?_, ?_⟩
    · rcases hlow_u m with h | h
      · exact absurd h hm
      · exact_mod_cast h
    by_contra hno
    push_neg at hno
    have hall : ∀ m : ℤ, (zeroSeries D' u₀.1).coeff m = 0 ∨ (((1 : ℕ) : ℤ) + 1) ≤ padicValRat p ((zeroSeries D' u₀.1).coeff m) := by
      intro m
      rcases hlow_u m with h | h
      · left; exact h
      · right
        have hne : (zeroSeries D' u₀.1).coeff m ≠ 0 := by intro h0; rw [h0] at h; simp at h
        have := hno m hne
        push_cast; omega
    have hm1 : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ 1))⁻¹ * D'.t u₀.1 ∈ (zeroChart Γ).integers := by
      rw [pow_one, hrow₁]; exact hmem₁
    have h0 := hupper u₀.1 1 hall hm1
    have h1 : (zeroChart Γ).residue ⟨_, hm1⟩ = (lam u₀)⁻¹ • hfun Γ := by
      rw [← hres₁']; exact chart_residue_congr _ _ _ (by rw [pow_one, hrow₁])
    rw [h1] at h0
    exact (smul_ne_zero (inv_ne_zero hlamu₀) hhfun0) h0
  have hRES_T_ne : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩ + algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (cN : (IsLocalRing.ResidueField ↥A)) ≠ 0 := by
    intro h0
    have hrel : ∑ j ∈ ({T, z} : Finset (Fin r)), (if j = T then (1 : (IsLocalRing.ResidueField ↥A)) else (cN : (IsLocalRing.ResidueField ↥A))) • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ = 0 := by
      rw [Finset.sum_pair hTz, if_pos rfl, if_neg hTz.symm, one_smul, hRES_z, ← Algebra.algebraMap_eq_smul_one]
      exact h0
    have := linearIndependent_iff'.mp hLI {T, z} (fun j => if j = T then (1 : (IsLocalRing.ResidueField ↥A)) else (cN : (IsLocalRing.ResidueField ↥A))) hrel T
      (Finset.mem_insert_self _ _)
    beta_reduce at this
    rw [if_pos rfl] at this
    exact one_ne_zero this
  have hcont_T : IsContent D' T ((2 : ℕ) : ℤ) := by
    refine ⟨fun m hm => ?_, ?_⟩
    · rcases hlow_T m with h | h
      · exact absurd h hm
      · exact_mod_cast h
    by_contra hno
    push_neg at hno
    have hall : ∀ m : ℤ, (zeroSeries D' T).coeff m = 0 ∨ (((2 : ℕ) : ℤ) + 1) ≤ padicValRat p ((zeroSeries D' T).coeff m) := by
      intro m
      rcases hlow_T m with h | h
      · left; exact h
      · right
        have hne : (zeroSeries D' T).coeff m ≠ 0 := by intro h0; rw [h0] at h; simp at h
        have := hno m hne
        push_cast; omega
    have hm2 : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ 2))⁻¹ * D'.t T ∈ (zeroChart Γ).integers := by
      rw [hrow₂]; exact hmem₂
    have h0 := hupper T 2 hall hm2
    have h1 : (zeroChart Γ).residue ⟨_, hm2⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩ + algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (cN : (IsLocalRing.ResidueField ↥A)) := by
      rw [← hres₂']; exact chart_residue_congr _ _ _ (by rw [hrow₂])
    rw [h1] at h0
    exact hRES_T_ne h0
  have hexp_u : hasseExp D' u₀.1 = 1 := hasseExp_eq_of_isContent hcont_u
  have hexp_T : hasseExp D' T = 2 := hasseExp_eq_of_isContent hcont_T
  have hexp' : ∀ l, hasseExp D' l = hasseExp Φ.toFamData l := by
    intro l
    by_cases hlu : l = u₀.1
    · rw [hlu, hexp_u, hnu₀]
    by_cases hlT : l = T
    · rw [hlT, hexp_T, hnT]
    exact hasseExp_eq_of_zeroSeries_eq (hz_other l hlu hlT)

  have hgfz_u : goodFamilyZero D' u₀.1 = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ))))⁻¹ * D'.t u₀.1 := by
    unfold goodFamilyZero; rw [hexp_u, pow_one]
  have hgfz_T : goodFamilyZero D' T = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ 2))⁻¹ * D'.t T := by
    unfold goodFamilyZero; rw [hexp_T]
  have hgfz_other : ∀ l, l ≠ u₀.1 → l ≠ T → goodFamilyZero D' l = goodFamilyZero Φ.toFamData l := by
    intro l hlu hlT
    unfold goodFamilyZero; rw [hexp' l, ht_other l hlu hlT]
  have hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers := by
    intro l
    by_cases hlu : l = u₀.1
    · rw [hlu, hgfz_u, hrow₁]; exact hmem₁
    by_cases hlT : l = T
    · rw [hlT, hgfz_T, hrow₂]; exact hmem₂
    rw [hgfz_other l hlu hlT]; exact hint l
  have hRES'_u : (zeroChart Γ).residue ⟨goodFamilyZero D' u₀.1, hint' u₀.1⟩ = (lam u₀)⁻¹ • hfun Γ := by
    rw [← hres₁']; exact chart_residue_congr _ _ _ (by rw [hgfz_u, hrow₁])
  have hRES'_T : (zeroChart Γ).residue ⟨goodFamilyZero D' T, hint' T⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩ + algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (cN : (IsLocalRing.ResidueField ↥A)) := by
    rw [← hres₂']; exact chart_residue_congr _ _ _ (by rw [hgfz_T, hrow₂])
  have hRES'_other : ∀ l, l ≠ u₀.1 → l ≠ T →
      (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩ = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ := by
    intro l hlu hlT
    exact chart_residue_congr _ _ _ (hgfz_other l hlu hlT)

  let RES' : Fin r → ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := fun l => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩
  have hRES'z : RES' z = 1 := by
    show (zeroChart Γ).residue ⟨goodFamilyZero D' z, hint' z⟩ = 1
    rw [hRES'_other z huz.symm hTz.symm, hRES_z]
  have hspan : ∀ j, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range RES') := by
    intro j
    by_cases hju : j = u₀.1
    · have hdecomp : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData u₀.1, hint u₀.1⟩ = RES' u₀.1 -
          ∑ i ∈ Finset.univ.erase u₀, (lam i * (lam u₀)⁻¹) • RES' i.1 := by
        have h1 : ∑ i : {l : Fin r // hasseExp Φ.toFamData l ≤ 1}, (lam i * (lam u₀)⁻¹) • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩
            = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData u₀.1, hint u₀.1⟩ + ∑ i ∈ Finset.univ.erase u₀, (lam i * (lam u₀)⁻¹) • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩ := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u₀), mul_inv_cancel₀ hlamu₀, one_smul]
        have h2 : ∀ i ∈ Finset.univ.erase u₀, (lam i * (lam u₀)⁻¹) • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i.1, hint i.1⟩ = (lam i * (lam u₀)⁻¹) • RES' i.1 := by
          intro i hi
          have hiu : (i.1 : Fin r) ≠ u₀.1 := fun h => Finset.ne_of_mem_erase hi (Subtype.ext h)
          have hiT : (i.1 : Fin r) ≠ T := by intro h; have := i.2; rw [h, hnT] at this; omega
          show _ = _ • (zeroChart Γ).residue ⟨goodFamilyZero D' i.1, hint' i.1⟩
          rw [hRES'_other i.1 hiu hiT]
        rw [Finset.sum_congr rfl h2] at h1
        have h3 : RES' u₀.1 = (lam u₀)⁻¹ • hfun Γ := hRES'_u
        rw [h3, ← hlam', h1]; abel
      rw [hju, hdecomp]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨u₀.1, rfl⟩) (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, rfl⟩))
    by_cases hjT : j = T
    · have hdecomp : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩ = RES' T - (cN : (IsLocalRing.ResidueField ↥A)) • RES' z := by
        show _ = (zeroChart Γ).residue ⟨goodFamilyZero D' T, hint' T⟩ - _
        rw [hRES'_T, hRES'z, Algebra.algebraMap_eq_smul_one]; abel
      rw [hjT, hdecomp]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨T, rfl⟩) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, rfl⟩))
    · have : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ = RES' j := (hRES'_other j hju hjT).symm
      rw [this]; exact Submodule.subset_span ⟨j, rfl⟩
  have hLI' : LinearIndependent (IsLocalRing.ResidueField ↥A) RES' := by
    haveI : FiniteDimensional (IsLocalRing.ResidueField ↥A) (Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range RES')) :=
      FiniteDimensional.span_of_finite (IsLocalRing.ResidueField ↥A) (Set.finite_range RES')
    let v' : Fin r → Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range RES') := fun j => ⟨(zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩, hspan j⟩
    have hv'LI : LinearIndependent (IsLocalRing.ResidueField ↥A) v' :=
      LinearIndependent.of_comp (Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range RES')).subtype (by exact hLI)
    have h1 : Fintype.card (Fin r) ≤ Module.finrank (IsLocalRing.ResidueField ↥A) (Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range RES')) := hv'LI.fintype_card_le_finrank
    have h2 : Module.finrank (IsLocalRing.ResidueField ↥A) (Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range RES')) ≤ Fintype.card (Fin r) := finrank_range_le_card RES'
    exact linearIndependent_iff_card_eq_finrank_span.mpr (le_antisymm h1 h2)

  have haRow_filt : ∀ j, max 0 ((hasseExp Φ.toFamData u₀.1 : ℤ) - (hasseExp Φ.toFamData j : ℤ))
      ≤ padicValRat p (aRow j) ∨ aRow j = 0 := by
    intro j
    rw [hnu₀]
    rcases haRow_val j with h | h
    · right; exact h
    · left; push_cast; exact max_le h.1 h.2
  have hb_filt : (2 : ℤ) ≤ padicValRat p bEnt ∨ bEnt = 0 := hbEnt_val.symm
  have hUfilt := matU_bifiltered p (fun l => hasseExp Φ.toFamData l) hnu₀ hnT hnz huT huz hTz haRow_u₀ haRow_filt hb_filt
    (u₀ := u₀.1) (T := T) (z := z) (a := aRow) (b := bEnt)
  have hVfilt := matV_bifiltered p (fun l => hasseExp Φ.toFamData l) hnu₀ hnT hnz huT huz hTz haRow_u₀ haRow_filt hb_filt
    (u₀ := u₀.1) (T := T) (z := z) (a := aRow) (b := bEnt)

  have hUint : ∀ i j, algebraMap ℚ (AlgebraicClosure ℚ) (U i j) ∈ A := by
    intro i j
    rw [eq_ratCast]
    apply ratCast_mem_of_padicValRat_nonneg hA
    rcases hUfilt i j with h | h
    · right; exact le_trans (le_max_left _ _) h
    · left; exact h

  have hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers := by
    intro l
    rw [ht]
    exact (chart_residue_sum (infChart Γ) (fun j : Fin r => Φ.t j) hintI (fun j : Fin r => algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) (hUint l)).1
  have hresI : ∀ l, (infChart Γ).residue ⟨D'.t l, hintI' l⟩
      = ∑ j, IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U l j), hUint l j⟩ • (infChart Γ).residue ⟨Φ.t j, hintI j⟩ := by
    intro l
    obtain ⟨hm, hres⟩ := chart_residue_sum (infChart Γ) (fun j : Fin r => Φ.t j) hintI (fun j : Fin r => algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) (hUint l)
    rw [← hres]; exact chart_residue_congr _ _ _ (ht l)
  have hres_infz : (infChart Γ).residue ⟨Φ.t z, hintI z⟩ = 1 := hres0 z hz
  have hres_infP : ∀ j : Fin r, 1 ≤ (j : ℕ) → (infChart Γ).residue ⟨Φ.t j, hintI j⟩
      = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P j) := fun j hj => (hP j hj).2

  have hresU_rat : ∀ (q : ℚ) (hq : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A), (q = 0 ∨ 1 ≤ padicValRat p q) →
      IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hq⟩ = 0 := by
    intro q hq h
    have hq' : ((q : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by rwa [eq_ratCast] at hq
    rw [show (⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hq⟩ : ↥A) = ⟨_, hq'⟩ from Subtype.ext (by push_cast [eq_ratCast]; rfl)]
    exact residue_eq_zero_of_padicValRat_pos hA q h hq'
  have hresU_nat : ∀ (m : ℕ) (hq : algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ) ∈ A),
      IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ), hq⟩ = (m : (IsLocalRing.ResidueField ↥A)) := by
    intro m hq
    have hq' : (((m : ℚ) : ℚ) : (AlgebraicClosure ℚ)) ∈ A := by rwa [eq_ratCast] at hq
    rw [show (⟨algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ), hq⟩ : ↥A) = ⟨_, hq'⟩ from Subtype.ext (by push_cast [eq_ratCast]; rfl)]
    exact residue_natCast' hA m hq'

  have hss : ssPolyBar Γ = Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) (∏ e' : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e'))) :=
    ssPolyBar_eq_aeval' p A Γ
  have hssmult : (∏ e' : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e'))).rootMultiplicity 0 = 1 := by
    have := rootMultiplicity_prod_X_sub_C' p A Γ e
    rwa [he] at this
  have hssne : (∏ e' : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e'))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e' _ => Polynomial.X_sub_C_ne_zero _
  have hord_of_numerator : ∀ (R : Polynomial (IsLocalRing.ResidueField ↥A)), R.eval 0 ≠ 0 →
      (nodeTgt Γ e).ord (ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) R) = 1 := by
    intro R hR
    have hR0 : R ≠ 0 := by rintro rfl; exact hR (Polynomial.eval_zero)
    show (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord _ = 1
    rw [he, hss, show Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) R = Polynomial.aeval (jB (IsLocalRing.ResidueField ↥A)) R from rfl, ← _root_.map_mul,
      ord_charLGeomPlaceOfPoint_aeval (IsLocalRing.ResidueField ↥A) 0 _ (mul_ne_zero hssne hR0), Polynomial.rootMultiplicity_mul (mul_ne_zero hssne hR0),
      hssmult, Polynomial.rootMultiplicity_eq_zero (fun h : Polynomial.IsRoot R 0 => hR h)]
    simp
  let coefR : Fin r → (IsLocalRing.ResidueField ↥A) := fun j => if j = T then (ν : (IsLocalRing.ResidueField ↥A))
    else if (1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData j ≤ 1) then ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) else 0
  have hresaRow : ∀ j, IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U u₀.1 j), hUint u₀.1 j⟩ • (infChart Γ).residue ⟨Φ.t j, hintI j⟩
      = coefR j • (ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P j)) := by
    intro j
    have hUj : U u₀.1 j = aRow j := hUu j
    by_cases hjT : j = T
    · subst hjT
      have h1 : IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U u₀.1 j), hUint u₀.1 j⟩ = (ν : (IsLocalRing.ResidueField ↥A)) := by
        have e1 : U u₀.1 j = ((ν : ℕ) : ℚ) := by rw [hUj, haRow_T]
        have hm : algebraMap ℚ (AlgebraicClosure ℚ) ((ν : ℕ) : ℚ) ∈ A := by have := hUint u₀.1 j; rwa [e1] at this
        rw [residueA_congr _ hm (congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) e1), hresU_nat ν hm]
      rw [h1, hres_infP j hT1]; simp [coefR]
    by_cases hj1 : 1 ≤ (j : ℕ)
    · by_cases hj : hasseExp Φ.toFamData j ≤ 1
      · have hn1 : hasseExp Φ.toFamData j = 1 := le_antisymm hj (hn_ge1 j hj1)
        have e1 : U u₀.1 j = ((liftN j : ℕ) : ℚ) := by rw [hUj, haRow_le j hjT hj, hn1]; simp
        have hm : algebraMap ℚ (AlgebraicClosure ℚ) ((liftN j : ℕ) : ℚ) ∈ A := by have := hUint u₀.1 j; rwa [e1] at this
        have h1 : IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U u₀.1 j), hUint u₀.1 j⟩ = ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) := by
          rw [residueA_congr _ hm (congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) e1), hresU_nat _ hm]
        rw [h1, hres_infP j hj1]; simp [coefR, hjT, hj1, hj]
      · have e1 : U u₀.1 j = 0 := by rw [hUj, haRow_out j hjT hj]
        have h1 : IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U u₀.1 j), hUint u₀.1 j⟩ = 0 := hresU_rat _ _ (Or.inl e1)
        rw [h1, zero_smul]; simp [coefR, hjT, hj]
    ·
      have hjz : (j : ℕ) = 0 := by omega
      have hn0 : hasseExp Φ.toFamData j = 0 := hn_z j hjz
      have e1 : U u₀.1 j = (p : ℚ) * (liftN j : ℚ) := by rw [hUj, haRow_le j hjT (by rw [hn0]; exact Nat.zero_le _), hn0]; simp
      have h1 : IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U u₀.1 j), hUint u₀.1 j⟩ = 0 := by
        apply hresU_rat
        by_cases hL : liftN j = 0
        · left; rw [e1, hL]; simp
        · right; rw [e1, padicValRat.mul (Nat.cast_ne_zero.mpr hprime.ne_zero) (Nat.cast_ne_zero.mpr hL), hvp]
          have := hvnat _ hL; omega
      rw [h1, zero_smul]; simp [coefR, hjT, hj1]
  have hresI_u : (infChart Γ).residue ⟨D'.t u₀.1, hintI' u₀.1⟩
      = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (∑ j, coefR j • P j) := by
    rw [hresI, Finset.sum_congr rfl (fun j _ => hresaRow j), _root_.map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul, Algebra.mul_smul_comm])
  have hR₁eval : (∑ j, coefR j • P j).eval 0 ≠ 0 := by
    rw [Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_smul, smul_eq_mul]
    have hsplit : ∑ j, coefR j * (P j).eval 0
        = (ν : (IsLocalRing.ResidueField ↥A)) * (P T).eval 0 +
          ∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData j ≤ 1 then ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) * (P j).eval 0 else 0) := by
      rw [← Finset.add_sum_erase _ (fun j => coefR j * (P j).eval 0) (Finset.mem_univ T)]
      have hT' : ∑ j : Fin r, (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData j ≤ 1 then ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) * (P j).eval 0 else 0)
          = ∑ j ∈ Finset.univ.erase T,
              (if 1 ≤ (j : ℕ) ∧ hasseExp Φ.toFamData j ≤ 1 then ((liftN j : ℕ) : (IsLocalRing.ResidueField ↥A)) * (P j).eval 0 else 0) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T), if_neg (by rw [hnT]; omega), zero_add]
      rw [hT']
      congr 1
      · simp [coefR]
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjT : j ≠ T := Finset.ne_of_mem_erase hj
        simp only [coefR, if_neg hjT]
        split_ifs <;> simp
    rw [hsplit, add_comm]; exact hνgood
  have hord₁ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t u₀.1, hintI' u₀.1⟩) = 1 := by
    rw [hresI_u]; exact hord_of_numerator _ hR₁eval
  have hresI_T : (infChart Γ).residue ⟨D'.t T, hintI' T⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P T) := by
    rw [hresI, Fintype.sum_eq_add T z hTz (fun j hj => by
      have e1 : U T j = 0 := by rw [hUT]; simp [rowB, hj.1, hj.2]
      rw [hresU_rat _ _ (Or.inl e1), zero_smul])]
    have e1 : U T T = ((1 : ℕ) : ℚ) := by rw [hUT]; simp [rowB]
    have hm1 : algebraMap ℚ (AlgebraicClosure ℚ) ((1 : ℕ) : ℚ) ∈ A := by have := hUint T T; rwa [e1] at this
    have h1 : IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U T T), hUint T T⟩ = 1 := by
      rw [residueA_congr _ hm1 (congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) e1), hresU_nat 1 hm1, Nat.cast_one]
    have h2 : IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) (U T z), hUint T z⟩ = 0 := by
      apply hresU_rat
      have e2 : U T z = bEnt := by rw [hUT]; simp [rowB, hTz.symm]
      rw [e2]
      rcases hbEnt_val with h | h
      · left; exact h
      · right; omega
    rw [h1, h2, one_smul, zero_smul, add_zero, hres_infP T hT1]
  have hord₂ : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t T, hintI' T⟩) = 1 := by
    rw [hresI_T]; exact hord_of_numerator _ hPT0

  have hrat : ∀ v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1), v.IsRational := fun v => isRational_place_modularFunctionFieldC_one (IsLocalRing.ResidueField ↥A) v
  have hβ₁ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' u₀.1, hint' u₀.1⟩) = 0 := by
    rw [hRES'_u, hnode0, Algebra.smul_def, (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (0 : (IsLocalRing.ResidueField ↥A))).ord_mul
      ((_root_.map_ne_zero _).mpr (inv_ne_zero hlamu₀)) hhfun0, Place.ord_algebraMap, zero_add]
    exact ord_pt_hfun_zero Γ hN
  have hβ₂ : (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' T, hint' T⟩) ≤ 0 := by
    rw [hRES'_T]
    rcases hcNgood with hpole | ⟨hreg, hval⟩
    · by_cases hc0 : (cN : (IsLocalRing.ResidueField ↥A)) = 0
      · rw [hc0, map_zero, add_zero]; exact le_of_lt hpole
      · rw [ord_add_eq_of_lt _ (hunit T) (by rw [Place.ord_algebraMap]; exact hpole)]
        exact le_of_lt hpole
    · have hmem : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData T, hint T⟩ ∈ (nodeSrc Γ e).toValuationSubring := (nodeSrc Γ e).mem_of_ord_nonneg (hunit T) hreg
      have hv := hasValue_evalAt (nodeSrc Γ e) (hrat _) hmem
      have hv' := P2MF2J.HasValue.add hv (Place.hasValue_algebraMap (nodeSrc Γ e) (cN : (IsLocalRing.ResidueField ↥A)))
      exact le_of_eq (hv'.ord_eq_zero hval)

  have hval0 : (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' u₀.1, hint' u₀.1⟩) = (lam u₀)⁻¹ := by
    rw [hRES'_u, hnode0]
    apply evalAt_eq_of_hasValue (hrat _)
    rw [Algebra.smul_def]
    have h1 := hasValue_pt_hfun Γ (zero_not_mem_wOne Γ)
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hN), zero_mul, add_zero] at h1
    have := Place.HasValue.mul (Place.hasValue_algebraMap (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (0 : (IsLocalRing.ResidueField ↥A))) (lam u₀)⁻¹) h1
    rwa [mul_one] at this
  have hsep : ∀ Q ∈ (zeroChart Γ).dom,
      ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' u₀.1, hint' u₀.1⟩)
        ≠ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' u₀.1, hint' u₀.1⟩) := by
    intro Q hQ
    rw [hval0, hRES'_u, Algebra.smul_def]
    have hvn : (zeroChart Γ).placeMap Q ∉ (zeroChart Γ).nodes := (zeroChart Γ).placeMap_not_mem_nodes Q hQ
    rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (IsLocalRing.ResidueField ↥A) ((zeroChart Γ).placeMap Q) with ⟨x, hx⟩ | hx
    · rw [hx] at hvn ⊢
      have hxw : x ∉ wOne Γ := fun h => hvn (charLGeomPlaceOfPoint_mem_nodes_of_mem_wOne Γ h)
      have hx0 : x ≠ 0 := by rintro rfl; exact hvn h0node
      have h1 := hasValue_pt_hfun Γ hxw
      have h2 := Place.HasValue.mul (Place.hasValue_algebraMap (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x) (lam u₀)⁻¹) h1
      rw [evalAt_eq_of_hasValue (hrat _) h2]
      intro heq
      have : (1 + x ^ (wOne Γ).card * ((polW Γ).eval x)⁻¹) = 1 := by
        have := congrArg (fun t => lam u₀ * t) heq
        simpa [mul_inv_cancel_left₀ hlamu₀, ← mul_assoc, mul_inv_cancel₀ hlamu₀] using this
      rw [add_eq_left] at this
      exact (mul_ne_zero (pow_ne_zero _ hx0) (inv_ne_zero (polW_eval_ne_zero Γ hxw))) this
    · rw [hx]
      have h1 := hasValue_infty_hfun Γ hN
      have h2 := Place.HasValue.mul (Place.hasValue_algebraMap (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))) (lam u₀)⁻¹) h1
      rw [evalAt_eq_of_hasValue (hrat _) h2]
      intro heq
      have : (2 : (IsLocalRing.ResidueField ↥A)) = 1 := by
        have := congrArg (fun t => lam u₀ * t) heq
        simpa [← mul_assoc, mul_inv_cancel₀ hlamu₀] using this
      have h21 : (2 : (IsLocalRing.ResidueField ↥A)) - 1 = 0 := by rw [this, sub_self]
      norm_num at h21

  refine ⟨U, D', hint', hintI', u₀.1, T, hUunit, hUfilt, ?_, ?_, htRat, ht, hexp', ?_, hLI', hu₀1, hT1,
    hord₁, hord₂, hβ₁, hβ₂, ?_, hsep⟩
  ·
    intro i j; rw [hUinv]; exact hVfilt i j
  ·
    intro i j hi
    have hiz : i = z := Fin.ext (by rw [hi, hz])
    rw [hiz, hUother z huz.symm hTz.symm]
    by_cases hzj : z = j
    · subst hzj; rw [if_pos rfl, if_pos hz]
    · rw [if_neg hzj, if_neg (fun h => hzj (Fin.ext (by rw [hz, h])))]
  ·
    intro l
    unfold goodFamilyZero
    rw [hexp' l, ht l]
  · rw [hexp_u, hexp_T]; norm_num

end MainThm

end ModularCurve.MultCovering.P2Mhsep

p2m_open "ModularCurve~jBar" in p2m_open "ModularCurve.MultCovering~hasseContent_nonneg" in open AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero.ModularCurve _root_.P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero.ModularCurve.MultCovering in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (he : ssValue Γ e = 0) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (D' : FamData p r)
      (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers) (l₁ l₂ : Fin r),
      IsUnit U ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
        ∨ U i j = 0) ∧
      (∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
        ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      1 ≤ (l₁ : ℕ) ∧ 1 ≤ (l₂ : ℕ) ∧
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l₁, hintI' l₁⟩) = 1 ∧
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D'.t l₂, hintI' l₂⟩) = 1 ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩) = 0 ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D' l₂, hint' l₂⟩) ≤ 0 ∧
      hasseExp D' l₁ < hasseExp D' l₂ ∧
      ∀ Q ∈ (zeroChart Γ).dom,
        ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩)
          ≠ (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero D' l₁, hint' l₁⟩) :=
  ModularCurve.MultCovering.P2Mhsep.twoMembers_certificate p hp13 A hA Γ Δ Φ hint hLI e he

end S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_unimodular_famData_twoMembers_certificate_of_ssValue_eq_zero (solution)
