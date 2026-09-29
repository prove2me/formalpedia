-- Prove2me | solution 1 for ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6eb1d97d-f864-56f9-baa4-f7fa2a57d5d6

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_MultCovering_exists_chartCtx_separated_covering
import Theorems.Thm_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_nonempty_annCtx
import Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_orth_linearIndependent_zeroChart_residue
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_linearIndependent
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_lt_thirteen
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom
import Theorems.Thm_ModularCurve_MultCovering_jF_mem_infChart_integers
import Theorems.Thm_ModularCurve_MultCovering_jpF_mem_infChart_integers
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_jF
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_jpF
import Theorems.Thm_ModularCurve_MultCovering_mem_infChart_integers_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_eq_modularRedLocHom
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_coeffMap
import Theorems.Thm_ModularCurve_MultCovering_mem_infChart_integers_of_forall_coeff_mem
import Theorems.Thm_ModularCurve_MultCovering_infChart_mem_integers_residue_ne_zero_of_qCoeff
import Theorems.Thm_ModularCurve_MultCovering_mem_infChart_integers_iff
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_ne_zero_iff_exists_quotient
import Theorems.Thm_ModularCurve_MultCovering_not_isSSCentred_of_mem_infChart_dom
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_MultCovering_not_isSSCentred_of_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_cuspInftyBar_mem_infChart_dom
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_pow_modulusExp_eq_modulus_mul
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_modulus_eq_mul
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_isUnit_modulus_eq_mul_of_ssValue_ne
import Theorems.Thm_ModularCurve_MultCovering_infChart_chartData
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
import Theorems.Thm_ModularCurve_MultCovering_exists_famCtx
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord
import Theorems.Thm_AlgebraicCurve_ComponentChart_comap_fibreParam_laws
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_modulusExp
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_MultCovering_infChart_chartData_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_mul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_MultCovering_neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
import Theorems.Thm_ModularCurve_MultCovering_residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne
import Theorems.Thm_ModularCurve_MultCovering_evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom
import Theorems.Thm_ModularCurve_MultCovering_chartComparison_infChart_of_fibreCoord
import Theorems.Thm_ModularCurve_MultCovering_chartComparison_zeroChart_of_chartData_of_fibreCoord
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom

import Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates
import Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven
import Theorems.Thm_ModularCurve_MultCovering_forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.LevelOnePhi.instAddCommGroup WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.GaussReduction.isLocalHom_constToGauss instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve~genus"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar qExpand jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full modularFunctionFieldBar coeffMap coeffEmb coeffEmb_mem_laurentBaseChange ssJSet PlaceSpecialization.LevelOneProlongationPair instDecidableEqResidueFieldSemistable jqModC modularFunctionFieldC PlaceSpecialization frobOnPlacesGeomLevel frobNodePair ratFuncEquivCharLOneC charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar PlaceSpecialization.LevelOneProlongationPair.mem_chartFst_nodes_iff ssPlaces IsAffineGeomPlace MultCovering.AnnCtx jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne jWidth_pos jWidth_eq_one_or hasPrincipalDivisors_modularFunctionFieldC_of_perfectField ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue MultCovering.zeroChart_chartData_goodFamilyZero_of_linearIndependent MultCovering.zeroChart_chartData_goodFamilyZero_of_lt_thirteen MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom MultCovering.jF_mem_infChart_integers MultCovering.jpF_mem_infChart_integers MultCovering.infChart_residue_jF MultCovering.infChart_residue_jpF MultCovering.mem_infChart_integers_iff_coe_mem_modularLocalized MultCovering.infChart_residue_eq_modularRedLocHom MultCovering.infChart_residue_coeffMap MultCovering.mem_infChart_integers_of_forall_coeff_mem MultCovering.infChart_mem_integers_residue_ne_zero_of_qCoeff MultCovering.mem_infChart_integers_iff MultCovering.infChart_residue_ne_zero_iff_exists_quotient MultCovering.not_isSSCentred_of_mem_infChart_dom MultCovering.mem_zeroChart_nodes_iff MultCovering.not_isSSCentred_of_mem_zeroChart_dom MultCovering.cuspInftyBar_mem_infChart_dom MultCovering.AnnCtx.exists_mem_pow_modulusExp_eq_modulus_mul MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne MultCovering.linkMatrixInv_mul MultCovering.linkMatrix_mul_inv MultCovering.AnnCtx.exists_mem_modulus_eq_mul MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne MultCovering.infChart_chartData MultCovering.hasseExp_zero MultCovering.one_le_hasseExp MultCovering.zeroChart_residue_goodFamilyZero_ne_zero exists_uniform_window_smul_mem_integers_of_qCoeff_criterion PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord MultCovering.hasseExp_le_modulusExp MultCovering.infChart_chartData_goodFamily MultCovering.exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos MultCovering.eq_sum_linkMatrix_mul_goodFamily MultCovering.linkBudget_spec MultCovering.neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero MultCovering.residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom MultCovering.chartComparison_infChart_of_fibreCoord MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord isCurveOver_modularFunctionFieldBar MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom MultCovering.exists_unimodular_famData_wideCertificates MultCovering.exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.hasseExp_eq_jWidth_of_genus_zero MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.eq_mAnnuli_add_one_of_isEmbBasis"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jF jpF tieG jBar nCharts mAnnuli modulusExp Fbar IsSSCentred ChartCtx infChart zeroChart chart chart_zero chart_one src tgt ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq edgeOf ssValue_edgeOf nodeSrc nodeTgt Statement StatementAll StatementAll_congr AnnCtx AnnCtx.modulus_eq hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst exists_chartCtx_separated_covering mem_infChart_dom_xor_mem_zeroChart_dom nonempty_annCtx exists_famCtx_orth_linearIndependent_zeroChart_residue zeroChart_chartData_goodFamilyZero_of_linearIndependent zeroChart_chartData_goodFamilyZero_of_lt_thirteen crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom jF_mem_infChart_integers jpF_mem_infChart_integers infChart_residue_jF infChart_residue_jpF mem_infChart_integers_iff_coe_mem_modularLocalized infChart_residue_eq_modularRedLocHom infChart_residue_coeffMap mem_infChart_integers_of_forall_coeff_mem infChart_mem_integers_residue_ne_zero_of_qCoeff mem_infChart_integers_iff infChart_residue_ne_zero_iff_exists_quotient not_isSSCentred_of_mem_infChart_dom mem_zeroChart_nodes_iff not_isSSCentred_of_mem_zeroChart_dom cuspInftyBar_mem_infChart_dom AnnCtx.exists_mem_pow_modulusExp_eq_modulus_mul AnnCtx.exists_mem_dom_abv_evalAt_param_ne linkMatrixInv_mul linkMatrix_mul_inv AnnCtx.exists_mem_modulus_eq_mul AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne infChart_chartData hasseExp_zero one_le_hasseExp zeroChart_residue_goodFamilyZero_ne_zero hasseExp_le_modulusExp infChart_chartData_goodFamily exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos eq_sum_linkMatrix_mul_goodFamily linkBudget_spec neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom chartComparison_infChart_of_fibreCoord chartComparison_zeroChart_of_chartData_of_fibreCoord abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom exists_unimodular_famData_wideCertificates exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven hasseExp_and_ord_node_residue_of_eq_eleven forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth hasseExp_eq_jWidth_of_genus_zero exists_famCtx_toFamData_eq_of_bifiltered eq_mAnnuli_add_one_of_isEmbBasis"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

theorem mAnnuli_pos (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : 0 < mAnnuli p := by
  first
  | (unfold mAnnuli
     rcases Nat.lt_or_ge p 12 with h | h
     · interval_cases p <;> first | decide | (norm_num at hp)
     · have h1 : 1 ≤ p / 12 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
       exact Nat.add_pos_left (Nat.add_pos_left h1 _) _)

open Classical in

noncomputable def windowExp (p : ℕ) [Fact p.Prime] {r : ℕ} (s : Fin r → modularFunctionFieldBar (1 * p)) : ℕ :=
  if hs : IsEmbBasis (1 * p) s then
    Classical.choose (ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion
      (1 * p) s hs p Fact.out)
  else 0

section PerA

noncomputable def fibreCoordInf (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → modularFunctionFieldBar (1 * p) :=
  Classical.choose (ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord
    hA Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply)

noncomputable def fibreCoord (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (i : Fin nCharts) :
    Place (IsLocalRing.ResidueField ↥A) (Fbar A i) → modularFunctionFieldBar (1 * p) :=
  ![fibreCoordInf p A hA Γ, fun x => (frickeInvolutionBar (1 * p)).symm (fibreCoordInf p A hA Γ x)] i

theorem mem_infChart_integers_iff' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p)) :
    f ∈ (infChart Γ).integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
  first
  | exact ModularCurve.MultCovering.mem_infChart_integers_iff Γ f

theorem mem_infChart_integers_iff_coe_mem_modularLocalized' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p)) :
    f ∈ (infChart Γ).integers ↔
      (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A) := by
  first
  | exact ModularCurve.MultCovering.mem_infChart_integers_iff_coe_mem_modularLocalized Γ f

theorem mem_infChart_integers_of_forall_coeff_mem' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p))
    (hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A) :
    f ∈ (infChart Γ).integers := by
  first
  | exact ModularCurve.MultCovering.mem_infChart_integers_of_forall_coeff_mem Γ f hf

theorem infChart_residue_coeffMap' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * p)) :
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar (1 * p)) ∈ (infChart Γ).integers,
      (((infChart Γ).residue ⟨_, hint⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
  first
  | exact ModularCurve.MultCovering.infChart_residue_coeffMap Γ y hy

theorem infChart_residue_eq_modularRedLocHom' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)) :
    ∃ h : f ∈ (infChart Γ).integers,
      (((infChart Γ).residue ⟨f, h⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) =
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hf⟩ := by
  first
  | exact ModularCurve.MultCovering.infChart_residue_eq_modularRedLocHom Γ f hf

theorem infChart_residue_ne_zero_iff_exists_quotient' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p)) :
    (∃ h : f ∈ (infChart Γ).integers, (infChart Γ).residue ⟨f, h⟩ ≠ 0) ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
  first
  | exact ModularCurve.MultCovering.infChart_residue_ne_zero_iff_exists_quotient Γ f

theorem jF_mem_infChart_integers' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : jF p ∈ (infChart Γ).integers := by
  first
  | exact ModularCurve.MultCovering.jF_mem_infChart_integers Γ hA

theorem jpF_mem_infChart_integers' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : jpF p ∈ (infChart Γ).integers := by
  first
  | exact ModularCurve.MultCovering.jpF_mem_infChart_integers Γ hA

theorem infChart_residue_jF' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    (infChart Γ).residue ⟨jF p, jF_mem_infChart_integers' p hp5 A hA Γ Δ⟩
      = jBar (IsLocalRing.ResidueField ↥A) := by
  first
  | exact ModularCurve.MultCovering.infChart_residue_jF Γ hA _

theorem infChart_residue_jpF' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    (infChart Γ).residue ⟨jpF p, jpF_mem_infChart_integers' p hp5 A hA Γ Δ⟩
      = jBar (IsLocalRing.ResidueField ↥A) ^ p := by
  first
  | exact ModularCurve.MultCovering.infChart_residue_jpF Γ hA _

theorem infChart_residue_tieG (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∃ h : tieG p ∈ (infChart Γ).integers, (infChart Γ).residue ⟨tieG p, h⟩ = 0 := by
  have hj := jF_mem_infChart_integers' p hp5 A hA Γ Δ
  have hjp := jpF_mem_infChart_integers' p hp5 A hA Γ Δ
  have hmem : tieG p ∈ (infChart Γ).integers :=
    (infChart Γ).integers.sub_mem hjp ((infChart Γ).integers.pow_mem hj p)
  refine ⟨hmem, ?_⟩
  have e1 : (⟨tieG p, hmem⟩ : ↥(infChart Γ).integers) =
      ⟨jpF p, hjp⟩ - ⟨jF p, hj⟩ ^ p := Subtype.ext rfl
  rw [e1, map_sub, map_pow, infChart_residue_jpF' p hp5 A hA Γ Δ, infChart_residue_jF' p hp5 A hA Γ Δ, sub_self]

theorem mem_infChart_nodes_iff (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (x : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
    x ∈ (infChart Γ).nodes ↔
      ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a = x := by
  first
  | exact ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_chartFst_nodes_iff Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply x

theorem ord_charLGeomPlaceOfPoint_jBar_sub (k : Type) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord (jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c)
      = if c = a then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a c

theorem not_isSSCentred_of_mem_infChart_dom' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hW : W ∈ (infChart Γ).dom)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ¬ IsSSCentred p A W a := by
  first
  | exact ModularCurve.MultCovering.not_isSSCentred_of_mem_infChart_dom Γ W hW a ha

theorem mem_infChart_dom_xor_mem_zeroChart_dom' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hsep : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      W ∈ Γ.S₁ → frickeInvolutionBar (1 * p) • W ∉ Γ.S₁)
    (hcov : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) 1 Γ.data Γ.hKr
          (frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W →
      IsAffineGeomPlace (IsLocalRing.ResidueField ↥A) 1 (Γ.P.redFst W) → Γ.P.redFst W ∉ ssPlaces p 1 (IsLocalRing.ResidueField ↥A) →
      W ∈ Γ.S₁ ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
    (hW : ∀ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), ¬ IsSSCentred p A W a) :
    Xor' (W ∈ (infChart Γ).dom) (W ∈ (zeroChart Γ).dom) := by
  first
  | exact ModularCurve.MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom Γ hsep hcov W hW

theorem cuspInftyBar_mem_infChart_dom' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : cuspInftyBar (1 * p) ∈ (infChart Γ).dom := by
  first
  | exact ModularCurve.MultCovering.cuspInftyBar_mem_infChart_dom Γ

theorem infChart_chartData' {ι : Type} [Fintype ι] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (t : ι → modularFunctionFieldBar (1 * p)) (ht : ∀ l, t l ≠ 0) :
    ∃ B : ℕ, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ),
      ∀ l : ι, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
        ∃ h : c • t l ∈ (infChart Γ).integers, (infChart Γ).residue ⟨c • t l, h⟩ ≠ 0 := by
  first
  | (obtain ⟨B, hB⟩ := ModularCurve.MultCovering.infChart_chartData p t ht
     exact ⟨B, fun A hA _ _ Γ _ => hB A hA Γ⟩)

theorem mem_zeroChart_integers_iff (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p)) :
    f ∈ (zeroChart Γ).integers ↔ frickeInvolutionBar (1 * p) f ∈ (infChart Γ).integers := Iff.rfl

theorem zeroChart_residue_eq (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p)) (h : f ∈ (zeroChart Γ).integers) :
    (zeroChart Γ).residue ⟨f, h⟩
      = (infChart Γ).residue ⟨frickeInvolutionBar (1 * p) f, (mem_zeroChart_integers_iff p hp5 A hA Γ Δ f).mp h⟩ := by
  first
  | rfl

theorem mem_zeroChart_nodes_iff' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (x : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
    x ∈ (zeroChart Γ).nodes ↔
      ∃ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A),
        charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p) = x := by
  first
  | exact ModularCurve.MultCovering.mem_zeroChart_nodes_iff Γ x

theorem charP_residueField (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] : CharP (IsLocalRing.ResidueField ↥A) p :=
  ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA

theorem pow_p_injective (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    Function.Injective fun a : IsLocalRing.ResidueField ↥A => a ^ p := by
  haveI := charP_residueField p hp5 A hA
  intro a b h
  have h' : (a - b) ^ p = 0 := by rw [sub_pow_char, sub_eq_zero]; exact h
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h')

private theorem _root_.AlgebraicCurve.Place.ord_neg' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  have h1 : v.ord (-1 : F) = 0 := by
    have h := v.ord_mul (neg_ne_zero.mpr (one_ne_zero' F)) (neg_ne_zero.mpr (one_ne_zero' F))
    rw [neg_one_mul, neg_neg, v.ord_one] at h
    omega
  rw [← neg_one_mul, v.ord_mul (neg_ne_zero.mpr (one_ne_zero' F)) hf, h1, zero_add]

p2m_alias "P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.AlgebraicCurve.Place.ord_neg'" "AlgebraicCurve.Place.ord_neg'"
namespace IsSSCentred

private theorem _root_.ModularCurve.MultCovering.IsSSCentred.centre_unique {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))} {a a' : IsLocalRing.ResidueField ↥A}
    (h : IsSSCentred p A W a) (h' : IsSSCentred p A W a') : a = a' := by
  obtain ⟨⟨x, hx, hxo⟩, -⟩ := h
  obtain ⟨⟨x', hx', hxo'⟩, -⟩ := h'
  change 0 < W.ord (jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ)) at hxo
  change 0 < W.ord (jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x' : AlgebraicClosure ℚ)) at hxo'
  by_contra hne
  have hxx : (x : AlgebraicClosure ℚ) ≠ x' := fun e => hne (by rw [← hx, ← hx', Subtype.ext e])
  set f := jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ) with hf
  set g := jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x' : AlgebraicClosure ℚ) with hg
  have hf0 : f ≠ 0 := fun e => by rw [e, Place.ord_zero] at hxo; exact lt_irrefl _ hxo
  have hg0 : g ≠ 0 := fun e => by rw [e, Place.ord_zero] at hxo'; exact lt_irrefl _ hxo'
  have hsum : f + -g =
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((x' : AlgebraicClosure ℚ) - x) := by
    rw [hf, hg, map_sub]; ring
  have hc0 : (x' : AlgebraicClosure ℚ) - x ≠ 0 := sub_ne_zero.mpr hxx.symm
  have hsum0 : f + -g ≠ 0 := by
    rw [hsum]; exact (map_ne_zero _).mpr hc0
  have key := W.min_ord_le_ord_add hf0 (neg_ne_zero.mpr hg0) hsum0
  rw [W.ord_neg', hsum, W.ord_algebraMap] at key
  have : 0 < min (W.ord f) (W.ord g) := lt_min hxo hxo'
  omega

end IsSSCentred
p2m_export "ModularCurve.MultCovering" "IsSSCentred.centre_unique"

theorem not_isSSCentred_of_mem_zeroChart_dom' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hW : W ∈ (zeroChart Γ).dom)
    (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ¬ IsSSCentred p A W a := by
  first
  | exact ModularCurve.MultCovering.not_isSSCentred_of_mem_zeroChart_dom Γ W hW a ha

theorem node_is_end (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ i, ∀ x ∈ (chart Γ i).nodes, ∃ e,
    (⟨src p e, nodeSrc Γ e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar A j)) = ⟨i, x⟩ ∨
    (⟨tgt p e, nodeTgt Γ e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar A j)) = ⟨i, x⟩ := by
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · intro x hx
    rw [chart_zero] at hx
    obtain ⟨a, ha, rfl⟩ := (mem_infChart_nodes_iff p hp5 A hA Γ Δ x).mp hx
    obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
    refine ⟨e, Or.inr ?_⟩
    subst he
    rfl
  · intro x hx
    rw [chart_one] at hx
    obtain ⟨a, ha, rfl⟩ := (mem_zeroChart_nodes_iff' p hp5 A hA Γ Δ x).mp hx
    obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
    refine ⟨e, Or.inl ?_⟩
    subst he
    rfl

theorem end_unique (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ i, ∀ x ∈ (chart Γ i).nodes,
    ∀ E E' : Fin (mAnnuli p) ⊕ Fin (mAnnuli p),
    Sum.elim (fun e => (⟨src p e, nodeSrc Γ e⟩ :
        Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar A j)))
        (fun e => ⟨tgt p e, nodeTgt Γ e⟩) E = ⟨i, x⟩ →
    Sum.elim (fun e => (⟨src p e, nodeSrc Γ e⟩ :
        Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar A j)))
        (fun e => ⟨tgt p e, nodeTgt Γ e⟩) E' = ⟨i, x⟩ → E = E' := by
  intro i x _ E E' hE hE'
  have hEE := hE.trans hE'.symm
  have hinj := charLGeomPlaceOfPoint_injective (IsLocalRing.ResidueField ↥A)
  have h10 : ∀ e e' : Fin (mAnnuli p), src p e ≠ tgt p e' := fun e e' h => by
    have hv := congrArg Fin.val h
    simp [src, tgt] at hv
  rcases E with e | e <;> rcases E' with e' | e'
  · simp only [Sum.elim_inl] at hEE
    obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp hEE
    have h3 : charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p) =
        charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e' ^ p) := eq_of_heq h2
    rw [ssValue_injective Γ (pow_p_injective p hp5 A hA Γ Δ (hinj h3))]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hEE
    exact absurd (Sigma.mk.inj_iff.mp hEE).1 (h10 e e')
  · simp only [Sum.elim_inl, Sum.elim_inr] at hEE
    exact absurd (Sigma.mk.inj_iff.mp hEE).1.symm (h10 e' e)
  · simp only [Sum.elim_inr] at hEE
    obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp hEE
    have h3 : charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e) =
        charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e') := eq_of_heq h2
    rw [ssValue_injective Γ (hinj h3)]

theorem partition (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hsep : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      W ∈ Γ.S₁ → frickeInvolutionBar (1 * p) • W ∉ Γ.S₁)
    (hcov : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) 1 Γ.data Γ.hKr
          (frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W →
      IsAffineGeomPlace (IsLocalRing.ResidueField ↥A) 1 (Γ.P.redFst W) → Γ.P.redFst W ∉ ssPlaces p 1 (IsLocalRing.ResidueField ↥A) →
      W ∈ Γ.S₁ ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁) :
    ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
    (∃ i, P ∈ (chart Γ i).dom ∧ (∀ j, P ∈ (chart Γ j).dom → j = i) ∧
      ∀ e, P ∉ (Δ.annIn e).dom) ∨
    (∃ e, P ∈ (Δ.annIn e).dom ∧ (∀ e', P ∈ (Δ.annIn e').dom → e' = e) ∧
      ∀ i, P ∉ (chart Γ i).dom) := by
  intro P
  by_cases hc : ∃ e, IsSSCentred p A P (ssValue Γ e)
  · obtain ⟨e, he⟩ := hc
    refine Or.inr ⟨e, (Δ.mem_dom_iff e P).mpr he, ?_, ?_⟩
    · intro e' he'
      exact ssValue_injective Γ
        (((Δ.mem_dom_iff e' P).mp he').centre_unique he)
    · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · rw [chart_zero]
        exact fun h => not_isSSCentred_of_mem_infChart_dom' p hp5 A hA Γ Δ P h _ (ssValue_mem_ssJSet Γ e) he
      · rw [chart_one]
        exact fun h => not_isSSCentred_of_mem_zeroChart_dom' p hp5 A hA Γ Δ P h _ (ssValue_mem_ssJSet Γ e) he
  · push_neg at hc
    have hW : ∀ a ∈ ssJSet p (IsLocalRing.ResidueField ↥A), ¬ IsSSCentred p A P a := by
      intro a ha h
      obtain ⟨e, rfl⟩ := exists_ssValue_eq Γ a ha
      exact hc e h
    have hann : ∀ e, P ∉ (Δ.annIn e).dom := fun e h =>
      hc e ((Δ.mem_dom_iff e P).mp h)
    refine Or.inl ?_
    rcases mem_infChart_dom_xor_mem_zeroChart_dom' p hp5 A hA Γ Δ hsep hcov P hW with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · refine ⟨0, by rw [chart_zero]; exact h0, Fin.forall_fin_two.mpr ⟨fun _ => rfl, fun h => ?_⟩, hann⟩
      rw [chart_one] at h
      exact absurd h h1
    · refine ⟨1, by rw [chart_one]; exact h1, Fin.forall_fin_two.mpr ⟨fun h => ?_, fun _ => rfl⟩, hann⟩
      rw [chart_zero] at h
      exact absurd h h0

theorem infChart_mem_integers_residue_ne_zero_of_qCoeff' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (f : modularFunctionFieldBar (1 * p))
    (hf : ∀ n : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A)
    (hu : ∃ n : ℤ, IsUnit (⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hf n⟩ : ↥A)) :
    ∃ h : f ∈ (infChart Γ).integers, (infChart Γ).residue ⟨f, h⟩ ≠ 0 := by
  first
  | exact ModularCurve.MultCovering.infChart_mem_integers_residue_ne_zero_of_qCoeff Γ f hf hu

theorem isUnit_mk_iff_not_mem_nonunits' {K : Type*} [Field K] (A : ValuationSubring K) {x : K} (hx : x ∈ A) :
    IsUnit (⟨x, hx⟩ : A) ↔ x ∉ A.nonunits := by
  show IsUnit (⟨x, hx⟩ : A) ↔ ((⟨x, hx⟩ : A) : K) ∉ A.nonunits
  rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]

theorem gaussWindow (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∃ i, cuspInftyBar (1 * p) ∈ (chart Γ i).dom ∧
    ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ windowExp p s * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ windowExp p s * c⁻¹ ∈ A ∧
      ∃ h : c • s l ∈ (chart Γ i).integers, (chart Γ i).residue ⟨c • s l, h⟩ ≠ 0 := by
  classical
  refine ⟨0, ?_, fun l => ?_⟩
  · exact cuspInftyBar_mem_infChart_dom' p hp5 A hA Γ Δ
  · have hB : windowExp p s = Classical.choose
        (ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion (1 * p) s hs p Fact.out) := by
      rw [windowExp, dif_pos hs]
    have hspec := Classical.choose_spec
      (ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion (1 * p) s hs p Fact.out)
    have hcrit : ∀ f : modularFunctionFieldBar (1 * p), f ∈ riemannRochSpace (embDivisor (1 * p)) →
        (∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) →
        (∃ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits) →
        ∃ h : f ∈ (infChart Γ).integers, (infChart Γ).residue ⟨f, h⟩ ≠ 0 := by
      intro f _ hf hu
      obtain ⟨k, hk⟩ := hu
      exact infChart_mem_integers_residue_ne_zero_of_qCoeff' p hp5 A hA Γ Δ f hf
        ⟨k, (isUnit_mk_iff_not_mem_nonunits' A (hf k)).mpr hk⟩
    obtain ⟨c, hc0, h1, h2, h, hres⟩ := hspec A hA _ (infChart Γ) hcrit l
    rw [hB]
    exact ⟨c, hc0, h1, h2, h, hres⟩

theorem residueFields (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ i,
    HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar A i) ∧
    ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar A i), x.IsRational := by
  intro i
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A

  let eqv := ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)
  letI : Algebra (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A i) := eqv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A i) :=
    IsScalarTower.of_algebraMap_eq fun c => (eqv.commutes c).symm
  haveI : FiniteDimensional (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A i) := by
    let L : RatFunc (IsLocalRing.ResidueField ↥A) ≃ₗ[RatFunc (IsLocalRing.ResidueField ↥A)] Fbar A i :=
      { eqv.toRingEquiv.toAddEquiv with
        map_smul' := fun r y => by
          show eqv (r * y) = eqv r * eqv y
          exact map_mul eqv r y }
    exact L.finiteDimensional
  exact ⟨hasPrincipalDivisors_modularFunctionFieldC_of_perfectField (IsLocalRing.ResidueField ↥A) 1,
    fun x => Place.isRational_of_isAlgClosed x⟩

theorem connected (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : ∀ i j : Fin nCharts, Relation.ReflTransGen
    (fun a b : Fin nCharts => ∃ e : Fin (mAnnuli p),
      (src p e = a ∧ tgt p e = b) ∨ (src p e = b ∧ tgt p e = a)) i j := by
  first
  | (have e : Fin (mAnnuli p) := ⟨0, mAnnuli_pos p hp hp5⟩
     have h10 : Relation.ReflTransGen (fun a b : Fin nCharts => ∃ e : Fin (mAnnuli p),
         (src p e = a ∧ tgt p e = b) ∨ (src p e = b ∧ tgt p e = a)) 1 0 :=
       Relation.ReflTransGen.single ⟨e, Or.inl ⟨rfl, rfl⟩⟩
     have h01 : Relation.ReflTransGen (fun a b : Fin nCharts => ∃ e : Fin (mAnnuli p),
         (src p e = a ∧ tgt p e = b) ∨ (src p e = b ∧ tgt p e = a)) 0 1 :=
       Relation.ReflTransGen.single ⟨e, Or.inr ⟨rfl, rfl⟩⟩
     intro i j
     fin_cases i <;> fin_cases j
     · exact Relation.ReflTransGen.refl
     · exact h01
     · exact h10
     · exact Relation.ReflTransGen.refl)

theorem modulus_dvd' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  first
  | exact ModularCurve.MultCovering.AnnCtx.exists_mem_pow_modulusExp_eq_modulus_mul p A Γ Δ

theorem p_dvd_modulus' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a := by
  first
  | exact ModularCurve.MultCovering.AnnCtx.exists_mem_modulus_eq_mul p A Γ Δ

theorem isRational_place_modularFunctionFieldBar' (N : ℕ) [NeZero N]
    (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) : P.IsRational := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Module.Finite (AlgebraicClosure ℚ) P.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) P.ResidueField := Algebra.IsIntegral.of_finite _ _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := P.ResidueField)).2

theorem fibreCoords (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ i, ∀ P ∈ (chart Γ i).dom,
    ∃ h : fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
            (P.evalAt (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P)))
          ∈ (chart Γ i).integers,
      (chart Γ i).residue ⟨_, h⟩ ≠ 0 ∧
      ((chart Γ i).placeMap P).ord ((chart Γ i).residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
            (P.evalAt (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P)))) ∧
      ∀ Q ∈ (chart Γ i).dom, (chart Γ i).placeMap Q = (chart Γ i).placeMap P →
        Q ≠ P →
        Q.ord (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
              (P.evalAt (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P)))) = 0 := by
  have hT := Classical.choose_spec
    (ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord hA Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply)
  intro i
  fin_cases i
  · exact hT
  · intro P hP

    have hPrat : P.IsRational := isRational_place_modularFunctionFieldBar' (1 * p) P
    exact AlgebraicCurve.ComponentChart.comap_fibreParam_laws (frickeInvolutionBar (1 * p)) (infChart Γ) P
      hPrat
      (fibreCoordInf p A hA Γ ((infChart Γ).placeMap (frickeInvolutionBar (1 * p) • P)))
      (hT (frickeInvolutionBar (1 * p) • P) hP)

theorem crossComparison (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hpart : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      (∃ i, P ∈ (chart Γ i).dom) ∨ (∃ e, P ∈ (Δ.annIn e).dom)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
    (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
    ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      (∀ i, P ∈ (chart Γ i).dom → Q ∉ (chart Γ i).dom) →
      (∀ e, P ∈ (Δ.annIn e).dom → Q ∉ (Δ.annIn e).dom) →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  first
  | exact ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom p hp5 Φ s hs A hA Γ Δ hpart

theorem tie_srcLift' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    ∃ xl : ↥A, IsLocalRing.residue ↥A xl = a ∧
      ∃ h : jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (xl : AlgebraicClosure ℚ)
          ∈ (chart Γ (src p (edgeOf Γ a ha))).integers,
        0 < (nodeSrc Γ (edgeOf Γ a ha)).ord
          ((chart Γ (src p (edgeOf Γ a ha))).residue ⟨_, h⟩) := by
  first
  | exact ModularCurve.MultCovering.exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos p A hA Γ a ha

theorem tie_tgtLift (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    ∃ yl : ↥A, IsLocalRing.residue ↥A yl = a ^ p ∧
      ∃ h : jpF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (yl : AlgebraicClosure ℚ)
          ∈ (chart Γ (tgt p (edgeOf Γ a ha))).integers,
        0 < (nodeTgt Γ (edgeOf Γ a ha)).ord
          ((chart Γ (tgt p (edgeOf Γ a ha))).residue ⟨_, h⟩) := by
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective a
  refine ⟨x ^ p, by rw [map_pow, hx], ?_⟩
  have hjp := jpF_mem_infChart_integers' p hp5 A hA Γ Δ
  have hc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ)
      ∈ (infChart Γ).integers := ((infChart Γ).algebraMap_mem_iff _).mpr (x ^ p).2
  have hmem : jpF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ)
      ∈ (infChart Γ).integers := (infChart Γ).integers.sub_mem hjp hc
  refine ⟨hmem, ?_⟩

  haveI := charP_residueField p hp5 A hA
  haveI : CharP ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) p :=
    charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField ↥A) _).injective p
  have e1 : (⟨jpF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ), hmem⟩ :
      ↥(infChart Γ).integers) = ⟨jpF p, hjp⟩ - ⟨_, hc⟩ := Subtype.ext rfl
  have hres : (infChart Γ).residue ⟨_, hmem⟩ =
      (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ a) ^ p := by
    rw [e1, map_sub, infChart_residue_jpF' p hp5 A hA Γ Δ, (infChart Γ).residue_algebraMap (x ^ p), map_pow, hx, map_pow,
      ← sub_pow_char]

  show 0 < (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ (edgeOf Γ a ha))).ord
    ((infChart Γ).residue ⟨_, hmem⟩)
  rw [ssValue_edgeOf, hres, ← zpow_natCast, Place.ord_zpow, ord_charLGeomPlaceOfPoint_jBar_sub, if_pos rfl, mul_one]
  exact_mod_cast (Fact.out : p.Prime).pos

theorem tie (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (hp : p.Prime) (hpp : p ∣ 1 * p) :
    (letI : NeZero p := ⟨hp.ne_zero⟩;
     ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
      a ≠ 0 → a ≠ 1728 → ∃ e,
      (Δ.annIn e).param
        = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) hpp)⟩ :
                modularFunctionFieldBar (1 * p))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p ∧
      (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
        ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (xl : AlgebraicClosure ℚ)
            ∈ (chart Γ (src p e)).integers,
          0 < (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, h⟩)) ∧
      (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
        ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) hpp)⟩ :
                modularFunctionFieldBar (1 * p))
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (yl : AlgebraicClosure ℚ)
            ∈ (chart Γ (tgt p e)).integers,
          0 < (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨_, h⟩))) := by
  first
  | (intro a ha ha0 ha1728
     exact ⟨edgeOf Γ a ha,
       Δ.param_eq_tieG (edgeOf Γ a ha)
         (by rw [ssValue_edgeOf]; exact ha0) (by rw [ssValue_edgeOf]; exact ha1728),
       tie_srcLift' p hp5 A hA Γ Δ a ha ha0 ha1728, tie_tgtLift p hp5 A hA Γ Δ a ha ha0 ha1728⟩)

end PerA

section WsTwentyInterface

theorem goodFamily_ne_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) : ∀ i, goodFamily Φ i ≠ 0 :=
  fun i => Φ.t_basis.1.ne_zero i

theorem linkMatrixInv_mul' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    linkMatrixInv Φ s hs * linkMatrix Φ s hs = 1 := by
  first
  | exact ModularCurve.MultCovering.linkMatrixInv_mul Φ s hs

theorem linkMatrix_mul_inv' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    linkMatrix Φ s hs * linkMatrixInv Φ s hs = 1 := by
  first
  | exact ModularCurve.MultCovering.linkMatrix_mul_inv Φ s hs

theorem eq_sum_linkMatrix_smul_goodFamily' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ i, s i = ∑ j, linkMatrix Φ s hs i j • goodFamily Φ j := by
  intro i
  simp_rw [Algebra.smul_def]
  exact ModularCurve.MultCovering.eq_sum_linkMatrix_mul_goodFamily Φ s hs i

theorem linkBudget_spec' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ i j, (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j ∈ A :=
  ModularCurve.MultCovering.linkBudget_spec Φ s hs A hA

theorem goodFamily_zero_eq_one' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ i : Fin r, (i : ℕ) = 0 → goodFamily Φ i = 1 := Φ.t_zero

theorem goodFamily_isEmbBasis (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    IsEmbBasis (1 * p) (goodFamily Φ) := Φ.t_basis

theorem goodFamily_mem_riemannRochSpace (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ i, goodFamily Φ i ∈ riemannRochSpace (embDivisor (1 * p)) := by
  first
  | (intro i; rw [← Φ.t_basis.2]; exact Submodule.subset_span ⟨i, rfl⟩)

theorem one_le_hasseExp' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := ModularCurve.MultCovering.one_le_hasseExp p A hA Γ Φ

theorem hasseExp_zero' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ l : Fin r, (l : ℕ) = 0 → hasseExp Φ.toFamData l = 0 := ModularCurve.MultCovering.hasseExp_zero Φ

theorem jBar_sub_algebraMap_ne_zero (k : Type) [Field k] [DecidableEq k] (c : k) :
    jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jBar_sub k c c
  rw [h, Place.ord_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem jBar_ne_zero (k : Type) [Field k] [DecidableEq k] : jBar k ≠ 0 := by
  simpa using jBar_sub_algebraMap_ne_zero k 0

private theorem _root_.AlgebraicCurve.Place.ord_finset_prod {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

p2m_alias "P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.AlgebraicCurve.Place.ord_finset_prod" "AlgebraicCurve.Place.ord_finset_prod"

theorem ssPolyBar_ne_zero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ssPolyBar Γ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun e _ => jBar_sub_algebraMap_ne_zero _ _

theorem ord_nodeTgt_ssPolyBar (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ) = 1 := by
  rw [ssPolyBar, Place.ord_finset_prod _ _ _ (fun e' _ => jBar_sub_algebraMap_ne_zero _ _)]
  simp_rw [ord_charLGeomPlaceOfPoint_jBar_sub, (ssValue_injective Γ).eq_iff]
  simp [Finset.sum_ite_eq']

theorem ord_charLGeomPlaceOfPoint_aeval_jBar (k : Type) [Field k] [DecidableEq k] (a : k) (Q : Polynomial k)
    (hQ : Q ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (Polynomial.aeval (jBar k) Q) = Polynomial.rootMultiplicity a Q := by
  have hX : ratFuncEquivCharLOneC k RatFunc.X = jBar k := by
    apply Subtype.ext
    show ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k
    rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
    exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)
  have halg : algebraMap (Polynomial k) (RatFunc k) Q = Polynomial.aeval (RatFunc.X : RatFunc k) Q := by
    have h : (IsScalarTower.toAlgHom k (Polynomial k) (RatFunc k)) = Polynomial.aeval (RatFunc.X : RatFunc k) := by
      apply Polynomial.algHom_ext
      simp [RatFunc.algebraMap_X]
    exact DFunLike.congr_fun h Q
  have h1 : Polynomial.aeval (jBar k) Q =
      (ratFuncEquivCharLOneC k).toRingEquiv (algebraMap (Polynomial k) (RatFunc k) Q) := by
    rw [halg, ← hX]
    exact (Polynomial.aeval_algHom_apply (ratFuncEquivCharLOneC k).toAlgHom RatFunc.X Q)
  rw [h1, show charLGeomPlaceOfPoint k a = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
      (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeOfPoint k a) from rfl,
    Place.ord_congrRingEquiv, RationalFunctionField.ord_placeOfPoint_algebraMap a hQ]

theorem ord_charLGeomPlaceOfPoint_aeval_jBar_eq_zero (k : Type) [Field k] [DecidableEq k] (a : k)
    (Q : Polynomial k) (hQa : Q.eval a ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (Polynomial.aeval (jBar k) Q) = 0 := by
  have hQ : Q ≠ 0 := fun h => hQa (by rw [h, Polynomial.eval_zero])
  rw [ord_charLGeomPlaceOfPoint_aeval_jBar k a Q hQ]
  exact_mod_cast Polynomial.rootMultiplicity_eq_zero hQa

theorem aeval_jBar_injective (k : Type) [Field k] :
    Function.Injective (Polynomial.aeval (R := k) (jBar k)) := by
  have htr : Transcendental k (jBar k) :=
    (transcendental_algebraMap_iff
      (algebraMap (↥(modularFunctionFieldC k 1)) (LaurentSeries k)).injective).mp (transcendental_jqModC k)
  exact transcendental_iff_injective.mp htr

theorem infChart_residue_goodFamily' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∃ hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers,
      (∀ i : Fin r, (i : ℕ) = 0 → (infChart Γ).residue ⟨goodFamily Φ i, hint i⟩ = 1) ∧
      ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          (P l).natDegree + 1 ≤ mAnnuli p ∧
          (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩
            = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
        Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
          = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
  first
  | exact Φ.t_inf A hA Γ

theorem infChart_goodFamily_residue_ne_zero' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∃ hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers,
      ∀ i, (infChart Γ).residue ⟨goodFamily Φ i, hint i⟩ ≠ 0 := by
  obtain ⟨hint, h0, P, hP, hli, -⟩ := infChart_residue_goodFamily' p hp5 A hA Γ Δ Φ s hs
  refine ⟨hint, fun i => ?_⟩
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · rw [h0 i hi]; exact one_ne_zero
  · rw [(hP i hi).2]
    have hPi : P i ≠ 0 := hli.ne_zero ⟨i, hi⟩
    exact mul_ne_zero (ssPolyBar_ne_zero p hp5 A hA Γ Δ)
      ((map_ne_zero_iff _ (aeval_jBar_injective (IsLocalRing.ResidueField ↥A))).mpr hPi)

theorem zeroChart_goodFamilyZero_residue_ne_zero' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∃ hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers,
      ∀ i, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩ ≠ 0 := ModularCurve.MultCovering.zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ

theorem infChart_chartData_goodFamily' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∃ (hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (infChart Γ).dom, P.IsRational ∧ ((infChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (infChart Γ).dom,
        (infChart Γ).residue ⟨goodFamily Φ (cQ ((infChart Γ).placeMap P)), hint _⟩ ≠ 0) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ j,
        goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹
          ∈ (infChart Γ).integers) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ j,
        goodFamily Φ j * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (infChart Γ).dom,
        ∀ hmem : goodFamily Φ (iQ ((infChart Γ).placeMap P))
            * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers,
        ((infChart Γ).placeMap P).ord ((infChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (infChart Γ).dom, ∀ Q ∈ (infChart Γ).dom,
        (infChart Γ).placeMap P ≠ (infChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamily Φ j
              * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹ ∈ (infChart Γ).integers)
          (hmQ : ∀ j, goodFamily Φ j
              * (goodFamily Φ (cQ ((infChart Γ).placeMap Q)))⁻¹ ∈ (infChart Γ).integers),
        ∃ i j, ((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmP i⟩)
            * ((infChart Γ).placeMap Q).evalAt ((infChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((infChart Γ).placeMap P).evalAt ((infChart Γ).residue ⟨_, hmP j⟩)
            * ((infChart Γ).placeMap Q).evalAt ((infChart Γ).residue ⟨_, hmQ i⟩)) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P ∈ (infChart Γ).dom, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧
          μ (P.evalAt (goodFamily Φ l
            * (goodFamily Φ (cQ ((infChart Γ).placeMap P)))⁻¹)) = 1) := by
  first
  | exact ModularCurve.MultCovering.infChart_chartData_goodFamily p hp5 A hA Γ Φ

theorem zeroChart_chartData_goodFamilyZero (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (hAd : ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      LinearIndependent (IsLocalRing.ResidueField ↥A)
        (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) := by
  by_cases hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728
  · exact ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne p A hA Γ Φ hw1
  · by_cases h13 : 13 ≤ p
    · obtain ⟨hint, hLI⟩ := hAd
      exact ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_linearIndependent p h13 A hA Γ Φ hint hLI
    · exact ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_lt_thirteen p hp5 (lt_of_not_ge h13) A hA Γ Δ Φ hAd μ hμ hμA

theorem zeroChart_chartData_goodFamilyZero_of_hw1 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ (hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers)
      (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
        → Fin r),
      (∀ P ∈ (zeroChart Γ).dom, P.IsRational ∧ ((zeroChart Γ).placeMap P).IsRational) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)), hint _⟩
          ≠ 0) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ (zeroChart Γ).integers) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ j,
        goodFamilyZero Φ.toFamData j * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
          ∈ P.toValuationSubring) ∧
      (∀ P ∈ (zeroChart Γ).dom,
        ∀ hmem : goodFamilyZero Φ.toFamData (iQ ((zeroChart Γ).placeMap P))
            * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
              ∈ (zeroChart Γ).integers,
        ((zeroChart Γ).placeMap P).ord ((zeroChart Γ).residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
              (((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ (zeroChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (zeroChart Γ).placeMap P ≠ (zeroChart Γ).placeMap Q →
        ∀ (hmP : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap P)))⁻¹
                ∈ (zeroChart Γ).integers)
          (hmQ : ∀ j, goodFamilyZero Φ.toFamData j
              * (goodFamilyZero Φ.toFamData (cQ ((zeroChart Γ).placeMap Q)))⁻¹
                ∈ (zeroChart Γ).integers),
        ∃ i j, ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP i⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ j⟩)
          ≠ ((zeroChart Γ).placeMap P).evalAt ((zeroChart Γ).residue ⟨_, hmP j⟩)
            * ((zeroChart Γ).placeMap Q).evalAt ((zeroChart Γ).residue ⟨_, hmQ i⟩)) :=
  ModularCurve.MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne p A hA Γ Φ hw1

theorem chartComparison (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hAd : ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      LinearIndependent (IsLocalRing.ResidueField ↥A)
        (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
    (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
    ∀ i, ∀ P ∈ (chart Γ i).dom, ∀ Q ∈ (chart Γ i).dom, P ≠ Q →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      ((chart Γ i).placeMap P = (chart Γ i).placeMap Q →
        |prox μ (evalVec s P) (evalVec s Q)
            + Real.log (μ (P.evalAt (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P))
                - Q.evalAt (fibreCoord p hp5 A hA Γ Δ i ((chart Γ i).placeMap P))))|
          ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      ((chart Γ i).placeMap P ≠ (chart Γ i).placeMap Q →
        |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by
  intro μ hμ hμA
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  ·
    exact ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord p hp5 A hA Γ Δ Φ s hs
      (fibreCoord p hp5 A hA Γ Δ 0) (fibreCoords p hp5 A hA Γ Δ 0) μ hμ hμA
  ·

    obtain ⟨hint0, cQ, iQ, hrat, hcQ, hratio, hreg, himm, hsep⟩ :=
      zeroChart_chartData_goodFamilyZero p hp5 A hA Γ Δ Φ s hs hAd μ hμ hμA
    exact ModularCurve.MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord p hp5 A hA Γ Δ Φ s hs
      hint0 cQ iQ hrat hcQ hratio hreg himm hsep (fibreCoord p hp5 A hA Γ Δ 1) (fibreCoords p hp5 A hA Γ Δ 1) μ hμ hμA

theorem zeroChart_hasse_small (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ Q ∈ (zeroChart Γ).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        goodFamily Φ l ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ l)) < 1 := by

  intro μ hμA Q hQ l hl
  have hp : p.Prime := Fact.out
  obtain ⟨-, hmem⟩ := ModularCurve.MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom
    p A hA Γ Φ μ hμA Q hQ
  obtain ⟨hQmem, hle⟩ := hmem l
  refine ⟨hQmem, hle.trans_lt ?_⟩
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpos : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0

  have hpinv : (p : AlgebraicClosure ℚ)⁻¹ ∉ A := by
    intro h
    have h1 : A.valuation ((p : AlgebraicClosure ℚ)⁻¹) ≤ 1 := (A.valuation_le_one_iff _).mpr h
    have h2 : A.valuation (p : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
    have hv0 : 0 < A.valuation (p : AlgebraicClosure ℚ) :=
      zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hp0)
    rw [map_inv₀, inv_le_one₀ hv0] at h1
    exact not_lt.mpr h1 h2
  have hμp : 1 < μ ((p : AlgebraicClosure ℚ)⁻¹) := not_le.mp (fun h => hpinv ((hμA _).mpr h))
  rw [map_inv₀, one_lt_inv₀ hpos] at hμp
  have hn := ModularCurve.MultCovering.one_le_hasseExp p A hA Γ Φ l hl
  calc μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l
      ≤ μ (p : AlgebraicClosure ℚ) ^ 1 := pow_le_pow_of_le_one hpos.le hμp.le hn
    _ = μ (p : AlgebraicClosure ℚ) := pow_one _
    _ < 1 := hμp

theorem infChart_nodeData' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∃ hint : ∀ i, goodFamily Φ i ∈ (infChart Γ).integers,
      ∀ e : Fin (mAnnuli p),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          1 ≤ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩)) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩) = 1) := by
  obtain ⟨hint, -, P, hP, hli, hspan⟩ := infChart_residue_goodFamily' p hp5 A hA Γ Δ Φ s hs

  have key : ∀ (e : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) →
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩)
        = 1 + Polynomial.rootMultiplicity (ssValue Γ e) (P l) := by
    intro e l hl1
    have hPl : P l ≠ 0 := hli.ne_zero ⟨l, hl1⟩
    have h1 := ssPolyBar_ne_zero p hp5 A hA Γ Δ
    have h2 : Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) ≠ 0 :=
      (map_ne_zero_iff _ (aeval_jBar_injective (IsLocalRing.ResidueField ↥A))).mpr hPl
    show (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord _ = _
    rw [(hP l hl1).2, (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord_mul h1 h2,
      ord_nodeTgt_ssPolyBar p hp5 A hA Γ Δ e, ord_charLGeomPlaceOfPoint_aeval_jBar _ _ _ hPl]
  refine ⟨hint, fun e => ⟨fun l hl1 => ?_, ?_⟩⟩
  · rw [key e l hl1]
    have := Int.natCast_nonneg (Polynomial.rootMultiplicity (ssValue Γ e) (P l))
    omega
  ·
    by_contra hne
    push_neg at hne
    have hall : ∀ l : {l : Fin r // 1 ≤ (l : ℕ)}, (P l).eval (ssValue Γ e) = 0 := by
      rintro ⟨l, hl1⟩
      by_contra hev
      apply hne l hl1
      rw [key e l hl1]
      have : Polynomial.rootMultiplicity (ssValue Γ e) (P l) = 0 := Polynomial.rootMultiplicity_eq_zero hev
      rw [this]; simp
    have h1 : (1 : Polynomial (IsLocalRing.ResidueField ↥A)) ∈
        Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
      rw [Polynomial.mem_degreeLT]
      exact Polynomial.degree_one_le.trans_lt (by exact_mod_cast mAnnuli_pos p Fact.out hp5)
    rw [← hspan] at h1
    have hev : ∀ f ∈ Submodule.span (IsLocalRing.ResidueField ↥A)
        (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l), f.eval (ssValue Γ e) = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf => obtain ⟨l, rfl⟩ := hf; exact hall l
      | zero => exact Polynomial.eval_zero
      | add f g _ _ hf hg => rw [Polynomial.eval_add, hf, hg, add_zero]
      | smul c f _ hf => rw [Polynomial.eval_smul, hf, smul_zero]
    exact one_ne_zero ((Polynomial.eval_one (x := ssValue Γ e)).symm.trans (hev 1 h1))

theorem zeroChart_nodeData (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    (∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) ∧
    ∀ e : Fin (mAnnuli p), ∃ (le : Fin r) (_ : 1 ≤ (le : ℕ)) (hint : goodFamily Φ le ∈ (infChart Γ).integers),
      (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ le, hint⟩) = 1 ∧
      ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i : Fin r, ∃ h0 : goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹ ∈ (zeroChart Γ).integers,
          (zeroChart Γ).residue ⟨_, h0⟩ ∈ (nodeSrc Γ e).toValuationSubring ∧
          ∀ R ∈ (Δ.annIn e).dom, ∃ hmem : R.evalAt (goodFamilyZero Φ.toFamData i * (goodFamilyZero Φ.toFamData le)⁻¹) ∈ A,
            IsLocalRing.residue ↥A ⟨_, hmem⟩ = (nodeSrc Γ e).evalAt ((zeroChart Γ).residue ⟨_, h0⟩) := by
  refine ⟨ModularCurve.MultCovering.neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero p A hA Γ Δ Φ hw1, fun e => ?_⟩
  obtain ⟨hint, hnd⟩ := infChart_nodeData' p hp5 A hA Γ Δ Φ s hs
  obtain ⟨le, hle, hord⟩ := (hnd e).2
  exact ⟨le, hle, hint le, hord, fun μ hμA =>
    ModularCurve.MultCovering.residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne
      p A hA Γ Δ Φ hw1 e le hle (hint le) hord μ hμA⟩

theorem annIn_modulus_eq_p_mul_unit' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (he0 : ssValue Γ e ≠ 0) (he1728 : ssValue Γ e ≠ 1728) :
    ∃ u : ↥A, IsUnit u ∧ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u := by
  first
  | exact ModularCurve.MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne p A Γ Δ e he0 he1728

theorem annIn_wide' (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∃ Q₁ ∈ (Δ.annIn e).dom, ∃ Q₂ ∈ (Δ.annIn e).dom,
        μ (Q₁.evalAt (Δ.annIn e).param) ≠ μ (Q₂.evalAt (Δ.annIn e).param) := by
  first
  | exact fun μ hμ => ModularCurve.MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne Δ e μ hμ

end WsTwentyInterface

theorem exists_rootCtx (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] :
    ∃ Γ : ChartCtx p A,
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
        W ∈ Γ.S₁ → frickeInvolutionBar (1 * p) • W ∉ Γ.S₁) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
        frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) 1 Γ.data Γ.hKr
            (frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W →
        IsAffineGeomPlace (IsLocalRing.ResidueField ↥A) 1 (Γ.P.redFst W) → Γ.P.redFst W ∉ ssPlaces p 1 (IsLocalRing.ResidueField ↥A) →
        W ∈ Γ.S₁ ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁) ∧
      Nonempty (AnnCtx Γ) := by
  obtain ⟨Γ, hsep, hcov⟩ := exists_chartCtx_separated_covering p hp5 A hA
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact ⟨Γ, hsep, hcov, nonempty_annCtx p hp5 A Γ⟩

theorem mainAll (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) :
    StatementAll p hp (1 * p) (dvd_mul_left p 1) := by
  intro r s hs
  obtain ⟨Φ, horthInf, horthZero, hAdapt⟩ :=
    ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue p hp5 s hs
  first
  | (refine ⟨nCharts, mAnnuli p, windowExp p s, modulusExp, compConst Φ s hs, mAnnuli_pos p hp hp5,
      fun A hA inst => ?_⟩

     obtain rfl : inst = ModularCurve.instDecidableEqResidueFieldSemistable A := Subsingleton.elim _ _
     letI : DecidableEq (IsLocalRing.ResidueField ↥A) := ModularCurve.instDecidableEqResidueFieldSemistable A
     haveI : CharP (IsLocalRing.ResidueField ↥A) p := charP_residueField p hp5 A hA
     obtain ⟨Γ, hsep, hcov, ⟨Δ⟩⟩ := exists_rootCtx p hp5 A hA
     exact ⟨Fbar A, fun i => inferInstance, fun i => inferInstance, chart Γ, Δ.annIn,
      Δ.annOut, src p, tgt p, nodeSrc Γ, nodeTgt Γ,
      fibreCoord p hp5 A hA Γ Δ, Δ.twoEnded, Δ.attached, node_is_end p hp5 A hA Γ Δ,
      end_unique p hp5 A hA Γ Δ, partition p hp5 A hA Γ Δ hsep hcov, gaussWindow p hp5 Φ s hs A hA Γ Δ,
      residueFields p hp5 A hA Γ Δ, connected p hp hp5, modulus_dvd' p hp5 A hA Γ Δ,
      p_dvd_modulus' p hp5 A hA Γ Δ, fibreCoords p hp5 A hA Γ Δ, chartComparison p hp5 Φ s hs A hA Γ Δ (hAdapt A hA Γ),
      crossComparison p hp5 Φ s hs A hA Γ Δ
        (fun P => (partition p hp5 A hA Γ Δ hsep hcov P).imp (fun h => ⟨h.choose, h.choose_spec.1⟩) (fun h => ⟨h.choose, h.choose_spec.1⟩)),
      tie p hp5 A hA Γ Δ hp (dvd_mul_left p 1)⟩)

def StatementWith (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar lvl) : Prop :=
    ∃ (n m B k : ℕ) (Cc : ℝ) (t : Fin r → modularFunctionFieldBar lvl)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ), 0 < m ∧
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) ∧
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (M i j) * t j) ∧
    Minv * M = 1 ∧ M * Minv = 1 ∧
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) ∧ (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) ∧ (∀ l, nexp l ≤ k) ∧
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar lvl) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar lvl)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar lvl),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar lvl ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) ∧
      (∀ e, ∀ l : Fin r, ∃ h : t l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩))) ∧
      (∀ e, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩) = 1) ∧
      (∀ e, ∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l
          ∈ (C (src e)).integers, (C (src e)).residue ⟨_, h⟩ ≠ 0) ∧
      (∀ e, ∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        t l ∈ R.toValuationSubring ∧ ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)) ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u))

def StatementAllWith (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) : Prop :=
  ∀ {r : ℕ} (s : Fin r → modularFunctionFieldBar lvl), IsEmbBasis lvl s → StatementWith p hp lvl hpl s

theorem StatementAllWith_congr (p : ℕ) (hp : p.Prime) {l₁ l₂ : ℕ} [NeZero l₁] [NeZero l₂] (h : l₁ = l₂)
    (h₁ : p ∣ l₁) (h₂ : p ∣ l₂) : StatementAllWith p hp l₁ h₁ → StatementAllWith p hp l₂ h₂ := by
  subst h
  exact id

theorem ex_linkBudget (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∀ i j, (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ linkBudget Φ s hs * linkMatrixInv Φ s hs i j ∈ A :=
  linkBudget_spec Φ s hs A hA

theorem ex_infEnds (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ e, ∀ l : Fin r, ∃ h : goodFamily Φ l ∈ (chart Γ (tgt p e)).integers,
      (chart Γ (tgt p e)).residue ⟨goodFamily Φ l, h⟩ ≠ 0 ∧
        (1 ≤ (l : ℕ) → 1 ≤ (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, h⟩)) := by
  obtain ⟨hint, hne⟩ := infChart_goodFamily_residue_ne_zero' p hp5 A hA Γ Δ Φ s hs
  obtain ⟨hint', hnode⟩ := infChart_nodeData' p hp5 A hA Γ Δ Φ s hs
  intro e l
  exact ⟨hint l, hne l, fun hl => (hnode e).1 l hl⟩

theorem ex_infEnds_one (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ e, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : goodFamily Φ l ∈ (chart Γ (tgt p e)).integers,
      (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, h⟩) = 1 := by
  obtain ⟨hint, hnode⟩ := infChart_nodeData' p hp5 A hA Γ Δ Φ s hs
  intro e
  obtain ⟨l, hl, h1⟩ := (hnode e).2
  exact ⟨l, hl, hint l, h1⟩

theorem ex_zeroEnds (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ e : Fin (mAnnuli p), ∀ l : Fin r,
      ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
          * goodFamily Φ l ∈ (chart Γ (src p e)).integers,
        (chart Γ (src p e)).residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨hint, hne⟩ := zeroChart_goodFamilyZero_residue_ne_zero' p hp5 A hA Γ Δ Φ s hs
  intro e l
  exact ⟨hint l, hne l⟩

theorem ex_tubeSmall (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s) :
    ∀ e, ∀ R ∈ (Δ.annIn e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        goodFamily Φ l ∈ R.toValuationSubring ∧ ∃ h : R.evalAt (goodFamily Φ l) ∈ A, (⟨R.evalAt (goodFamily Φ l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  first
  | exact ModularCurve.MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom p A hA Γ Δ Φ

theorem ex_tieWith (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (hp : p.Prime) (hpp : p ∣ 1 * p) :
    (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (Δ.annIn e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) hpp)⟩ :
                modularFunctionFieldBar (1 * p))
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p)) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (xl : AlgebraicClosure ℚ)
              ∈ (chart Γ (src p e)).integers,
            0 < (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) hpp)⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (yl : AlgebraicClosure ℚ)
              ∈ (chart Γ (tgt p e)).integers,
            0 < (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨_, h⟩)) ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u)) := by
  first
  | (intro a ha ha0 ha1728
     have he0 : ssValue Γ (edgeOf Γ a ha) ≠ 0 := by rw [ssValue_edgeOf]; exact ha0
     have he1728 : ssValue Γ (edgeOf Γ a ha) ≠ 1728 := by rw [ssValue_edgeOf]; exact ha1728
     obtain ⟨u, hu, hmod⟩ := ModularCurve.MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne p A Γ Δ
       (edgeOf Γ a ha) he0 he1728
     refine ⟨edgeOf Γ a ha, Δ.param_eq_tieG (edgeOf Γ a ha) he0 he1728,
       tie_srcLift' p hp5 A hA Γ Δ a ha ha0 ha1728, tie_tgtLift p hp5 A hA Γ Δ a ha ha0 ha1728,
       (u : AlgebraicClosure ℚ), u.2, ?_, hmod⟩
     obtain ⟨v, hv⟩ := hu.exists_right_inv
     have : ((u : AlgebraicClosure ℚ))⁻¹ = (v : AlgebraicClosure ℚ) := by
       rw [inv_eq_of_mul_eq_one_right]
       exact_mod_cast hv
     rw [this]; exact v.2)

theorem mainAllWith (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) :
    StatementAllWith p hp (1 * p) (dvd_mul_left p 1) := by
  intro r s hs
  obtain ⟨Φ, horthInf, horthZero, hAdapt⟩ :=
    ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue p hp5 s hs

  obtain ⟨A₀, hA₀⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
  letI : DecidableEq (IsLocalRing.ResidueField ↥A₀) := ModularCurve.instDecidableEqResidueFieldSemistable A₀
  haveI : CharP (IsLocalRing.ResidueField ↥A₀) p := charP_residueField p hp5 A₀ hA₀
  obtain ⟨Γ₀, -, -, ⟨Δ₀⟩⟩ := exists_rootCtx p hp5 A₀ hA₀
  refine ⟨nCharts, mAnnuli p, windowExp p s, modulusExp, compConst Φ s hs,
    goodFamily Φ, linkMatrix Φ s hs, linkMatrixInv Φ s hs, fun l => hasseExp Φ.toFamData l, linkBudget Φ s hs,
    mAnnuli_pos p hp hp5,
    goodFamily_zero_eq_one' p hp5 Φ s hs,
    ModularCurve.MultCovering.eq_sum_linkMatrix_mul_goodFamily Φ s hs,
    ModularCurve.MultCovering.linkMatrixInv_mul Φ s hs,
    ModularCurve.MultCovering.linkMatrix_mul_inv Φ s hs,
    hasseExp_zero' p hp5 Φ s hs,
    ModularCurve.MultCovering.one_le_hasseExp p A₀ hA₀ Γ₀ Φ,
    ModularCurve.MultCovering.hasseExp_le_modulusExp p A₀ hA₀ Γ₀ Δ₀ Φ,
    fun A hA inst => ?_⟩
  obtain rfl : inst = ModularCurve.instDecidableEqResidueFieldSemistable A := Subsingleton.elim _ _
  letI : DecidableEq (IsLocalRing.ResidueField ↥A) := ModularCurve.instDecidableEqResidueFieldSemistable A
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := charP_residueField p hp5 A hA
  obtain ⟨Γ, hsep, hcov, ⟨Δ⟩⟩ := exists_rootCtx p hp5 A hA
  exact ⟨Fbar A, fun i => inferInstance, fun i => inferInstance, chart Γ, Δ.annIn,
    Δ.annOut, src p, tgt p, nodeSrc Γ, nodeTgt Γ,
    fibreCoord p hp5 A hA Γ Δ, Δ.twoEnded, Δ.attached, node_is_end p hp5 A hA Γ Δ,
    end_unique p hp5 A hA Γ Δ, partition p hp5 A hA Γ Δ hsep hcov, gaussWindow p hp5 Φ s hs A hA Γ Δ,
    residueFields p hp5 A hA Γ Δ, connected p hp hp5, modulus_dvd' p hp5 A hA Γ Δ,
    p_dvd_modulus' p hp5 A hA Γ Δ, fibreCoords p hp5 A hA Γ Δ, chartComparison p hp5 Φ s hs A hA Γ Δ (hAdapt A hA Γ),
    crossComparison p hp5 Φ s hs A hA Γ Δ
      (fun P => (partition p hp5 A hA Γ Δ hsep hcov P).imp (fun h => ⟨h.choose, h.choose_spec.1⟩) (fun h => ⟨h.choose, h.choose_spec.1⟩)),
    ex_linkBudget p hp5 Φ s hs A hA,
    ex_infEnds p hp5 A hA Γ Δ Φ s hs,
    ex_infEnds_one p hp5 A hA Γ Δ Φ s hs,
    ex_zeroEnds p hp5 A hA Γ Δ Φ s hs,
    ex_tubeSmall p hp5 A hA Γ Δ Φ s hs,
    ex_tieWith p hp5 A hA Γ Δ hp (dvd_mul_left p 1)⟩

def StatementWithCert (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar lvl) : Prop :=
    ∃ (n m B k : ℕ) (Cc : ℝ) (t : Fin r → modularFunctionFieldBar lvl)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ), 0 < m ∧
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) ∧
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (M i j) * t j) ∧
    Minv * M = 1 ∧ M * Minv = 1 ∧
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) ∧ (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) ∧ (∀ l, nexp l ≤ k) ∧
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar lvl) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar lvl)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar lvl),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar lvl ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) ∧
      (∀ e, ∀ l : Fin r, ∃ h : t l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩))) ∧
      (∀ e, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩) = 1) ∧
      (∀ e, ∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l
          ∈ (C (src e)).integers, (C (src e)).residue ⟨_, h⟩ ≠ 0) ∧
      (∀ e, ∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        t l ∈ R.toValuationSubring ∧ ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
      (∀ e, ∃ w : ℕ, 1 ≤ w ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          (((An e).modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) ∧
        (2 ≤ w →
          ∃ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar lvl),
            (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) ∧ (Uinv * U = 1 ∧ U * Uinv = 1) ∧
            (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (U l j) * t j) ∧
        (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * f l ∈ (C (src e)).integers,
        (∀ l : Fin r, (C (src e)).residue ⟨_, hint l⟩ ≠ 0) ∧
        (∀ l : Fin r, (xs e).ord ((C (src e)).residue ⟨_, hint l⟩) = -((nexp l / w : ℕ) : ℤ)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (C (src e)).residue ⟨_, hint l⟩)) ∧
        (∀ l : Fin r, ∃ h : f l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩))) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩) = 1) ∧
        (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) ∧
        (∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
        ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩) = 1) ∧ nexp l = w) ∨
        (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f m₂, h⟩) = 1) ∧
        nexp m₁ < nexp m₂ ∧ nexp m₂ < w ∧ nexp m₁ + w ≤ 2 * nexp m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl)
        ((p : AlgebraicClosure ℚ) ^ nexp m₁))⁻¹ * f m₁ ∈ (C (src e)).integers) (c : IsLocalRing.ResidueField ↥A),
        (xs e).ord ((C (src e)).residue ⟨_, h⟩ - algebraMap (IsLocalRing.ResidueField ↥A) (Fbar (src e)) c) = 1))))) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)) ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u))

def StatementAllWithCert (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) : Prop :=
  ∀ {r : ℕ} (s : Fin r → modularFunctionFieldBar lvl), IsEmbBasis lvl s → StatementWithCert p hp lvl hpl s

theorem StatementAllWithCert_congr (p : ℕ) (hp : p.Prime) {l₁ l₂ : ℕ} [NeZero l₁] [NeZero l₂] (h : l₁ = l₂)
    (h₁ : p ∣ l₁) (h₂ : p ∣ l₂) : StatementAllWithCert p hp l₁ h₁ → StatementAllWithCert p hp l₂ h₂ := by
  subst h
  exact id

theorem ratCast_mem_of_padicValRat_nonneg (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (q : ℚ) (hq : 0 ≤ padicValRat p q) :
    algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
  rw [eq_ratCast (algebraMap ℚ (AlgebraicClosure ℚ)) q]
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [Rat.cast_zero]; exact zero_mem A
  · exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A (Fact.out : p.Prime)
      ((ValuationSubring.mem_nonunits_iff (A := A)).mp hA) hq0).mpr hq

theorem tube_ratCast_mem_maximalIdeal (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (q : ℚ) (hq : 0 < padicValRat p q ∨ q = 0)
    (h : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A) :
    (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rcases hq with hq | rfl
  · have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    have hdiv : 0 ≤ padicValRat p (q / p) := by
      rw [padicValRat.div hq0 hp, padicValRat.self (Fact.out : p.Prime).one_lt]; omega
    have hmem : algebraMap ℚ (AlgebraicClosure ℚ) (q / p) ∈ A :=
      ratCast_mem_of_padicValRat_nonneg p A hA _ hdiv
    have key : (⟨_, h⟩ : ↥A) = (p : ↥A) * ⟨_, hmem⟩ := by
      apply Subtype.ext
      show algebraMap ℚ (AlgebraicClosure ℚ) q = ((p : ↥A) : AlgebraicClosure ℚ) * algebraMap ℚ (AlgebraicClosure ℚ) (q / p)
      rw [show ((p : ↥A) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) from rfl,
        ← map_natCast (algebraMap ℚ (AlgebraicClosure ℚ)) p, ← map_mul, mul_div_cancel₀ _ hp]
    rw [key]
    exact Ideal.mul_mem_right _ _ (ValuationSubring.natCast_mem_maximalIdeal_of_liesOverPrime hA)
  · have h0 : (⟨_, h⟩ : ↥A) = 0 := Subtype.ext (by simp)
    rw [h0]; exact Ideal.zero_mem _

theorem ratCast_mem_maximalIdeal_of_padicValRat_pos (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) (q : ℚ) (hq : 0 < padicValRat p q ∨ q = 0) :
    ∃ h : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  have h : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
    rcases hq with hq | rfl
    · exact ratCast_mem_of_padicValRat_nonneg p A hA q hq.le
    · rw [map_zero]; exact zero_mem A
  exact ⟨h, tube_ratCast_mem_maximalIdeal p A hA q hq h⟩

theorem tube_evalAt_eq_of_residue_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) {a : K}
    (ha : IsLocalRing.residue ↥v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a) :
    v.evalAt f = a := by
  rw [v.evalAt_of_mem hf, ha, v.residueInv_algebraMap]

theorem tube_residue_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (a : K) :
    IsLocalRing.residue ↥v.toValuationSubring (algebraMap K ↥v.toValuationSubring a) = algebraMap K v.ResidueField a :=
  (IsScalarTower.algebraMap_apply K ↥v.toValuationSubring v.ResidueField a).symm

theorem tube_evalAt_sum_mul_mem_maximalIdeal {K F : Type*} [Field K] [Field F] [Algebra K F]
    (A : ValuationSubring K) (v : AlgebraicCurve.Place K F) (hv : v.IsRational) {r : ℕ} (c : Fin r → K) (t : Fin r → F)
    (hcA : ∀ j, c j ∈ A) (htS : ∀ j, t j ∈ v.toValuationSubring) (htA : ∀ j, v.evalAt (t j) ∈ A)
    (hsmall : ∀ j, (⟨c j, hcA j⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ∨
      (⟨v.evalAt (t j), htA j⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) :
    (∑ j, algebraMap K F (c j) * t j) ∈ v.toValuationSubring ∧
      ∃ h : v.evalAt (∑ j, algebraMap K F (c j) * t j) ∈ A,
        (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by

  set g : ↥v.toValuationSubring := ∑ j, algebraMap K ↥v.toValuationSubring (c j) * ⟨t j, htS j⟩ with hg_def
  have hg : (g : F) = ∑ j, algebraMap K F (c j) * t j := by
    simp [hg_def]
  have hfS : (∑ j, algebraMap K F (c j) * t j) ∈ v.toValuationSubring := hg ▸ g.2

  have hE : v.evalAt (∑ j, algebraMap K F (c j) * t j) = ∑ j, c j * v.evalAt (t j) := by
    apply tube_evalAt_eq_of_residue_eq v hfS
    have hsub : (⟨_, hfS⟩ : ↥v.toValuationSubring) = g := Subtype.ext hg.symm
    rw [hsub, hg_def, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, tube_residue_algebraMap, v.algebraMap_evalAt hv (htS j)]
  refine ⟨hfS, ?_⟩
  rw [hE]
  have hEA : (∑ j, c j * v.evalAt (t j)) ∈ A := sum_mem fun j _ => mul_mem (hcA j) (htA j)
  refine ⟨hEA, ?_⟩
  have hsub : (⟨_, hEA⟩ : ↥A) = ∑ j, (⟨c j, hcA j⟩ : ↥A) * ⟨v.evalAt (t j), htA j⟩ :=
    Subtype.ext (by push_cast; rfl)
  rw [hsub]
  refine Ideal.sum_mem _ fun j _ => ?_
  rcases hsmall j with hj | hj
  · exact Ideal.mul_mem_right _ _ hj
  · exact Ideal.mul_mem_left _ _ hj

theorem evalAt_sum_mem_maximalIdeal_of_mem_annIn_dom (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (u : Fin r → ℚ) (hu : ∀ j, 0 ≤ padicValRat p (u j)) (hu0 : ∀ j : Fin r, (j : ℕ) = 0 → 0 < padicValRat p (u j) ∨ u j = 0)
    (e : Fin (mAnnuli p)) (R : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hR : R ∈ (Δ.annIn e).dom) :
    (∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) (u j)) * goodFamily Φ j)
        ∈ R.toValuationSubring ∧
      ∃ h : R.evalAt (∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (algebraMap ℚ (AlgebraicClosure ℚ) (u j)) * goodFamily Φ j) ∈ A,
        (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  have hrat : R.IsRational := ((Δ.annIn e).mem_dom R hR).1
  have hT := ModularCurve.MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom p A hA Γ Δ Φ e R hR
  have h0 : ∀ j : Fin r, (j : ℕ) = 0 → goodFamily Φ j = 1 := fun j hj => Φ.t_zero j hj
  have hmemS : ∀ j : Fin r, goodFamily Φ j ∈ R.toValuationSubring := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
    · rw [h0 j hj]; exact one_mem _
    · exact (hT j hj).1
  have hmemA : ∀ j : Fin r, R.evalAt (goodFamily Φ j) ∈ A := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
    · rw [h0 j hj, AlgebraicCurve.Place.evalAt_one]; exact one_mem _
    · obtain ⟨h, -⟩ := (hT j hj).2
      exact h
  have hcA : ∀ j : Fin r, algebraMap ℚ (AlgebraicClosure ℚ) (u j) ∈ A :=
    fun j => ratCast_mem_of_padicValRat_nonneg p A hA (u j) (hu j)
  have hsmall : ∀ j : Fin r, (⟨_, hcA j⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A ∨
      (⟨R.evalAt (goodFamily Φ j), hmemA j⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
    · exact Or.inl (tube_ratCast_mem_maximalIdeal p A hA (u j) (hu0 j hj) (hcA j))
    · obtain ⟨h, hh⟩ := (hT j hj).2
      exact Or.inr hh
  exact tube_evalAt_sum_mul_mem_maximalIdeal A R hrat (fun j => algebraMap ℚ (AlgebraicClosure ℚ) (u j))
    (goodFamily Φ) hcA hmemS hmemA hsmall

theorem res_congr {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] {Γ : ChartCtx p A} (i : Fin nCharts)
    {x y : ↥(modularFunctionFieldBar (1 * p))} (hx : x ∈ (chart Γ i).integers) (hy : y ∈ (chart Γ i).integers) (h : x = y) :
    (chart Γ i).residue ⟨x, hx⟩ = (chart Γ i).residue ⟨y, hy⟩ := by
  subst h; rfl

set_option maxHeartbeats 6400000 in

theorem wideCert_ge_thirteen (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hp13 : 13 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (w : ℕ) (hw : w = jWidth (ssValue Γ e)) (hw2 : 2 ≤ w) :
    ∃ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar (1 * p)),
            (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) ∧ (Uinv * U = 1 ∧ U * Uinv = 1) ∧
            (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (U l j) * goodFamily Φ j) ∧
        (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * f l ∈ (chart Γ (src p e)).integers,
        (∀ l : Fin r, (chart Γ (src p e)).residue ⟨_, hint l⟩ ≠ 0) ∧
        (∀ l : Fin r, (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, hint l⟩) = -((hasseExp Φ.toFamData l / w : ℕ) : ℤ)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (chart Γ (src p e)).residue ⟨_, hint l⟩)) ∧
        (∀ l : Fin r, ∃ h : f l ∈ (chart Γ (tgt p e)).integers,
        (chart Γ (tgt p e)).residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩))) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩) = 1) ∧
        (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) ∧
        (∀ R ∈ (Δ.annIn e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
        ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩) = 1) ∧ hasseExp Φ.toFamData l = w) ∨
        (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f m₂, h⟩) = 1) ∧
        hasseExp Φ.toFamData m₁ < hasseExp Φ.toFamData m₂ ∧ hasseExp Φ.toFamData m₂ < w ∧ hasseExp Φ.toFamData m₁ + w ≤ 2 * hasseExp Φ.toFamData m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData m₁))⁻¹ * f m₁ ∈ (chart Γ (src p e)).integers) (c : IsLocalRing.ResidueField ↥A),
        (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, h⟩ - algebraMap (IsLocalRing.ResidueField ↥A) (Fbar A (src p e)) c) = 1))) := by
  classical
  have hwne1 : jWidth (ssValue Γ e) ≠ 1 := by omega
  obtain ⟨U, D', hint', hintI', hUunit, hU, hUinv, hU0, htRat, ht, hexp, hgfz, hLI', hex1, hex2, hne, hatt, hIwide, hIone,
    hItwo, hsep2, hunr⟩ :=
    ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates p hp13 A hA Γ Δ Φ hint hLI

  set φ : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ) with hφ
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hUunit

  have hUv : ∀ i j, 0 ≤ padicValRat p (U i j) := by
    intro i j
    rcases hU i j with h | h
    · exact le_trans (le_max_left _ _) h
    · rw [h, padicValRat.zero]
  have hUinvv : ∀ i j, 0 ≤ padicValRat p (U⁻¹ i j) := by
    intro i j
    rcases hUinv i j with h | h
    · exact le_trans (le_max_left _ _) h
    · rw [h, padicValRat.zero]

  have hsrc : chart Γ (src p e) = zeroChart Γ := rfl
  have htgt : chart Γ (tgt p e) = infChart Γ := rfl

  have hresc : ∀ l, (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * D'.t l
      = goodFamilyZero D' l := by
    intro l; rw [hgfz l, ht l]
  have hint'' : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * D'.t l
      ∈ (chart Γ (src p e)).integers := by
    intro l; rw [hresc l]; exact hint' l
  have hres'' : ∀ l, (chart Γ (src p e)).residue ⟨_, hint'' l⟩ = (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩ :=
    fun l => res_congr (Γ := Γ) (src p e) (hint'' l) (hint' l) (hresc l)
  refine ⟨U.map φ, U⁻¹.map φ, D'.t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j
    exact ⟨ratCast_mem_of_padicValRat_nonneg p A hA _ (hUv i j), ratCast_mem_of_padicValRat_nonneg p A hA _ (hUinvv i j)⟩
  ·
    constructor
    · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero φ) (map_one φ)]
  ·
    intro l; rw [ht l]; rfl
  ·
    refine ⟨hint'', fun l => ?_, fun l => ?_, ?_⟩
    · rw [hres'' l]; exact hLI'.ne_zero l
    · rw [hres'' l, hw]; exact hatt e l
    · have : (fun l => (chart Γ (src p e)).residue ⟨_, hint'' l⟩)
          = (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) := funext hres''
      rw [this]; exact hLI'
  ·
    intro l
    refine ⟨hintI' l, hne l, fun hl => ?_⟩
    exact le_of_eq (hIwide e l hl hwne1).symm
  ·
    obtain ⟨l, hl, hl1⟩ := hex1
    exact ⟨l, hl, hintI' l, hIone e l hl hl1⟩
  ·
    intro l hl
    rw [ht l]
    have hr : 0 < r := Fin.pos l
    have hsum : ∀ j : Fin r, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (φ (U l j)) * Φ.t j
        = if (j : ℕ) = 0 then 1 else 0 := by
      intro j
      rw [hU0 l j hl]
      by_cases hj : (j : ℕ) = 0
      · rw [if_pos hj, if_pos hj, map_one, map_one, Φ.t_zero j hj, mul_one]
      · rw [if_neg hj, if_neg hj, map_zero, map_zero, zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => hsum j)]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun j : Fin r => (j : ℕ) = 0)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨⟨0, hr⟩, ?_⟩
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj; exact Fin.ext hj
      · intro hj; rw [hj]
    rw [hcard]; simp
  ·
    intro R hR l hl
    have hu0 : ∀ j : Fin r, (j : ℕ) = 0 → 0 < padicValRat p (U l j) ∨ U l j = 0 := by
      intro j hj
      rcases hU l j with h | h
      · left
        have h0 : hasseExp Φ.toFamData j = 0 := ModularCurve.MultCovering.hasseExp_zero Φ j hj
        have h1 : 1 ≤ hasseExp Φ.toFamData l := ModularCurve.MultCovering.one_le_hasseExp p A hA Γ Φ l hl
        have : (1 : ℤ) ≤ max 0 ((hasseExp Φ.toFamData l : ℤ) - (hasseExp Φ.toFamData j : ℤ)) := by
          rw [h0]; push_cast; omega
        exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℤ) < 1) (le_trans this h)
      · right; exact h
    obtain ⟨hmem, hval⟩ := evalAt_sum_mem_maximalIdeal_of_mem_annIn_dom p A hA Γ Δ Φ (fun j => U l j) (hUv l) hu0 e R hR
    rw [ht l]
    exact ⟨hmem, hval⟩
  ·
    rcases jWidth_eq_one_or (ssValue Γ e) with h1 | h2 | h3
    · exact absurd h1 hwne1
    ·
      left
      obtain ⟨l₂, hl₂⟩ := hex2 ⟨e, hwne1⟩
      have hl₂1 : 1 ≤ (l₂ : ℕ) := by
        by_contra h0
        push Not at h0
        have : (l₂ : ℕ) = 0 := by omega
        have := ModularCurve.MultCovering.hasseExp_zero Φ l₂ this
        omega
      exact ⟨l₂, hl₂1, ⟨hintI' l₂, hIwide e l₂ hl₂1 hwne1⟩, by rw [hl₂, hw, h2]⟩
    ·
      right
      obtain ⟨m₁, hm₁, hm₁1⟩ := hex1
      obtain ⟨m₂, hm₂2⟩ := hex2 ⟨e, hwne1⟩
      have hm₂ : 1 ≤ (m₂ : ℕ) := by
        by_contra h0
        push Not at h0
        have : (m₂ : ℕ) = 0 := by omega
        have := ModularCurve.MultCovering.hasseExp_zero Φ m₂ this
        omega
      obtain ⟨c, hc⟩ := hunr e m₁ h3 hm₁ hm₁1
      refine ⟨m₁, m₂, hm₁, hm₂, ⟨hintI' m₁, hIone e m₁ hm₁ hm₁1⟩, ⟨hintI' m₂, hIwide e m₂ hm₂ hwne1⟩, ?_, ?_, ?_,
        ⟨hint'' m₁, c, ?_⟩⟩
      · rw [hm₁1, hm₂2]; norm_num
      · rw [hm₂2, hw, h3]; norm_num
      · rw [hm₁1, hm₂2, hw, h3]
      · rw [hres'' m₁]; exact hc

set_option maxHeartbeats 6400000 in

theorem wideCert_lt_thirteen (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hp13 : p < 13) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (w : ℕ) (hw : w = jWidth (ssValue Γ e)) (hw2 : 2 ≤ w) :
    ∃ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar (1 * p)),
            (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) ∧ (Uinv * U = 1 ∧ U * Uinv = 1) ∧
            (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (U l j) * goodFamily Φ j) ∧
        (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * f l ∈ (chart Γ (src p e)).integers,
        (∀ l : Fin r, (chart Γ (src p e)).residue ⟨_, hint l⟩ ≠ 0) ∧
        (∀ l : Fin r, (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, hint l⟩) = -((hasseExp Φ.toFamData l / w : ℕ) : ℤ)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (chart Γ (src p e)).residue ⟨_, hint l⟩)) ∧
        (∀ l : Fin r, ∃ h : f l ∈ (chart Γ (tgt p e)).integers,
        (chart Γ (tgt p e)).residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩))) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩) = 1) ∧
        (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) ∧
        (∀ R ∈ (Δ.annIn e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
        ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩) = 1) ∧ hasseExp Φ.toFamData l = w) ∨
        (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f m₂, h⟩) = 1) ∧
        hasseExp Φ.toFamData m₁ < hasseExp Φ.toFamData m₂ ∧ hasseExp Φ.toFamData m₂ < w ∧ hasseExp Φ.toFamData m₁ + w ≤ 2 * hasseExp Φ.toFamData m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData m₁))⁻¹ * f m₁ ∈ (chart Γ (src p e)).integers) (c : IsLocalRing.ResidueField ↥A),
        (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, h⟩ - algebraMap (IsLocalRing.ResidueField ↥A) (Fbar A (src p e)) c) = 1))) := by
  classical
  have hwne1 : jWidth (ssValue Γ e) ≠ 1 := by omega
  have hwpos : 0 < w := by omega
  obtain ⟨μ, hμ, -, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  have hr : r = mAnnuli p + 1 := ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis p hp5 s hs
  have hsrc : chart Γ (src p e) = zeroChart Γ := rfl
  have htgt : chart Γ (tgt p e) = infChart Γ := rfl
  have hprime : p.Prime := Fact.out
  by_cases hp11 : p = 11
  ·
    have hm : mAnnuli p = 2 := by subst hp11; decide
    have hr3 : r = 3 := by rw [hr, hm]
    subst hr3
    obtain ⟨U, D', hint', hUunit, hU, hUinv, hU0, htRat, ht, hexp, hgfz, hLI', hatt⟩ :=
      ModularCurve.MultCovering.exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven
        p hp11 A hA Γ Δ Φ hint hLI

    obtain ⟨Φ', hΦ'⟩ := ModularCurve.MultCovering.exists_famCtx_toFamData_eq_of_bifiltered p Φ horthInf horthZero U hUunit hU hUinv
      hU0 D' htRat ht hexp
    obtain ⟨hintI', hne'⟩ := infChart_goodFamily_residue_ne_zero' p hp5 A hA Γ Δ Φ' s hs
    obtain ⟨hintI'', hnode'⟩ := infChart_nodeData' p hp5 A hA Γ Δ Φ' s hs
    have hint'Φ : ∀ l, goodFamilyZero Φ'.toFamData l ∈ (zeroChart Γ).integers := by rw [hΦ']; exact hint'
    have hLIΦ : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : Fin 3 => (zeroChart Γ).residue ⟨goodFamilyZero Φ'.toFamData l, hint'Φ l⟩) := by
      have : (fun l : Fin 3 => (zeroChart Γ).residue ⟨goodFamilyZero Φ'.toFamData l, hint'Φ l⟩)
          = (fun l : Fin 3 => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) := by
        funext l; exact res_congr (Γ := Γ) 1 _ _ (by rw [hΦ'])
      rw [this]; exact hLI'
    obtain ⟨hintIP, l₂, l₃, hne23, hl₂, hl₃, hn2, hn3, hP⟩ :=
      ModularCurve.MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven p hp11 A hA Γ Δ Φ' hint'Φ hLIΦ μ hμA
    have htΦ : ∀ l, goodFamily Φ' l = D'.t l := fun l => by show Φ'.toFamData.t l = D'.t l; rw [hΦ']
    have hexpΦ : ∀ l, hasseExp Φ'.toFamData l = hasseExp Φ.toFamData l := fun l => by rw [hΦ']; exact hexp l
    rw [hexpΦ] at hn2 hn3

    have hI : ∀ l, D'.t l ∈ (infChart Γ).integers := fun l => htΦ l ▸ hintI' l
    have hresI : ∀ l (h₁ : goodFamily Φ' l ∈ (infChart Γ).integers),
        (infChart Γ).residue ⟨goodFamily Φ' l, h₁⟩ = (chart Γ (tgt p e)).residue ⟨D'.t l, hI l⟩ :=
      fun l h₁ => res_congr (Γ := Γ) 0 _ _ (htΦ l)
    set φ : ℚ →+* AlgebraicClosure ℚ := algebraMap ℚ (AlgebraicClosure ℚ) with hφ
    have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hUunit
    have hUv : ∀ i j, 0 ≤ padicValRat p (U i j) := by
      intro i j; rcases hU i j with h | h
      · exact le_trans (le_max_left _ _) h
      · rw [h, padicValRat.zero]
    have hUinvv : ∀ i j, 0 ≤ padicValRat p (U⁻¹ i j) := by
      intro i j; rcases hUinv i j with h | h
      · exact le_trans (le_max_left _ _) h
      · rw [h, padicValRat.zero]
    have hresc : ∀ l, (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * D'.t l
        = goodFamilyZero D' l := by
      intro l; rw [hgfz l, ht l]
    have hint'' : ∀ l : Fin 3, (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * D'.t l
        ∈ (chart Γ (src p e)).integers := by
      intro l; rw [hresc l]; exact hint' l
    have hres'' : ∀ l, (chart Γ (src p e)).residue ⟨_, hint'' l⟩ = (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩ :=
      fun l => res_congr (Γ := Γ) (src p e) (hint'' l) (hint' l) (hresc l)

    have hcase : (w = 2 ∧ ssValue Γ e = 1728) ∨ (w = 3 ∧ ssValue Γ e = 0) := by
      rcases jWidth_eq_one_or (ssValue Γ e) with h1 | h2 | h3
      · exact absurd h1 hwne1
      · left
        refine ⟨by rw [hw, h2], ?_⟩
        by_contra hne
        by_cases h0 : ssValue Γ e = 0
        · rw [jWidth_of_eq_zero h0] at h2; omega
        · rw [jWidth_of_ne h0 hne] at h2; omega
      · right
        refine ⟨by rw [hw, h3], ?_⟩
        by_contra h0
        by_cases h1728 : ssValue Γ e = 1728
        · rw [jWidth_of_eq_1728 h1728 h0] at h3; omega
        · rw [jWidth_of_ne h0 h1728] at h3; omega
    refine ⟨U.map φ, U⁻¹.map φ, D'.t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      exact ⟨ratCast_mem_of_padicValRat_nonneg p A hA _ (hUv i j), ratCast_mem_of_padicValRat_nonneg p A hA _ (hUinvv i j)⟩
    · constructor
      · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero φ) (map_one φ)]
      · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · intro l; rw [ht l]; rfl
    · refine ⟨hint'', fun l => ?_, fun l => ?_, ?_⟩
      · rw [hres'' l]; exact hLI'.ne_zero l
      · rw [hres'' l, hw]; exact hatt e l
      · have : (fun l => (chart Γ (src p e)).residue ⟨_, hint'' l⟩)
            = (fun l : Fin 3 => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) := funext hres''
        rw [this]; exact hLI'
    · intro l
      refine ⟨hI l, ?_, fun hl => ?_⟩
      · rw [← hresI l (hintI' l)]; exact hne' l
      · rw [← hresI l (hintI'' l)]; exact (hnode' e).1 l hl
    · obtain ⟨l, hl, hl1⟩ := (hnode' e).2
      exact ⟨l, hl, hI l, by rw [← hresI l (hintI'' l)]; exact hl1⟩
    · intro l hl
      rw [ht l]
      have hsum : ∀ j : Fin 3, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (φ (U l j)) * Φ.t j
          = if (j : ℕ) = 0 then 1 else 0 := by
        intro j
        rw [hU0 l j hl]
        by_cases hj : (j : ℕ) = 0
        · rw [if_pos hj, if_pos hj, map_one, map_one, Φ.t_zero j hj, mul_one]
        · rw [if_neg hj, if_neg hj, map_zero, map_zero, zero_mul]
      rw [Finset.sum_congr rfl (fun j _ => hsum j)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter (fun j : Fin 3 => (j : ℕ) = 0)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨0, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; rw [hj]; rfl
      rw [hcard]; simp
    · intro R hR l hl
      have hu0 : ∀ j : Fin 3, (j : ℕ) = 0 → 0 < padicValRat p (U l j) ∨ U l j = 0 := by
        intro j hj
        rcases hU l j with h | h
        · left
          have h0 : hasseExp Φ.toFamData j = 0 := ModularCurve.MultCovering.hasseExp_zero Φ j hj
          have h1 : 1 ≤ hasseExp Φ.toFamData l := ModularCurve.MultCovering.one_le_hasseExp p A hA Γ Φ l hl
          have : (1 : ℤ) ≤ max 0 ((hasseExp Φ.toFamData l : ℤ) - (hasseExp Φ.toFamData j : ℤ)) := by
            rw [h0]; push_cast; omega
          exact_mod_cast lt_of_lt_of_le (by norm_num : (0:ℤ) < 1) (le_trans this h)
        · right; exact h
      obtain ⟨hmem, hval⟩ := evalAt_sum_mem_maximalIdeal_of_mem_annIn_dom p A hA Γ Δ Φ (fun j => U l j) (hUv l) hu0 e R hR
      rw [ht l]
      exact ⟨hmem, hval⟩
    ·
      left
      rcases hcase with ⟨hw2', h1728⟩ | ⟨hw3, h0⟩
      · obtain ⟨h21, -, -⟩ := (hP e).1 h1728
        exact ⟨l₂, hl₂, ⟨hI l₂, by rw [← hresI l₂ (hintIP l₂)]; exact h21⟩, by rw [hn2, hw2']⟩
      · obtain ⟨h31, -⟩ := (hP e).2 h0
        exact ⟨l₃, hl₃, ⟨hI l₃, by rw [← hresI l₃ (hintIP l₃)]; exact h31⟩, by rw [hn3, hw3]⟩
  ·
    have hp57 : p = 5 ∨ p = 7 := by
      interval_cases p <;> first | (left; rfl) | (right; rfl) | exact absurd rfl hp11 | exact absurd hprime (by decide)
    have hm : mAnnuli p = 1 := by rcases hp57 with rfl | rfl <;> decide
    have hr2 : r = 2 := by rw [hr, hm]
    subst hr2
    obtain ⟨hintI, hneI⟩ := infChart_goodFamily_residue_ne_zero' p hp5 A hA Γ Δ Φ s hs
    obtain ⟨hintI2, hnode⟩ := infChart_nodeData' p hp5 A hA Γ Δ Φ s hs
    have hn1 : hasseExp Φ.toFamData 1 = jWidth (ssValue Γ e) :=
      ModularCurve.MultCovering.hasseExp_eq_jWidth_of_genus_zero p A hA Γ Δ Φ hint hLI μ hμA e

    have hord1 : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ 1, hintI2 1⟩) = 1 := by
      obtain ⟨l, hl, hl1⟩ := (hnode e).2
      have : l = 1 := by
        ext; have := l.isLt; simp only [Fin.val_one]; omega
      subst this; exact hl1
    obtain ⟨-, h0', hsrc1⟩ :=
      ModularCurve.MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
        p A hA Γ Δ Φ e 1 hn1 (hintI2 1) hord1 μ hμA
    have hresI : ∀ l (h₁ h₂ : goodFamily Φ l ∈ (infChart Γ).integers),
        (infChart Γ).residue ⟨goodFamily Φ l, h₁⟩ = (infChart Γ).residue ⟨goodFamily Φ l, h₂⟩ := fun _ _ _ => rfl

    have hf1 : ∀ l : Fin 2, Φ.t l = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((1 : Matrix (Fin 2) (Fin 2) (AlgebraicClosure ℚ)) l j) * Φ.t j := by
      intro l
      rw [Finset.sum_eq_single l]
      · rw [Matrix.one_apply_eq, map_one]; exact (one_mul _).symm
      · intro j _ hjl; rw [Matrix.one_apply_ne (Ne.symm hjl), map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ l) h
    have hint'' : ∀ l : Fin 2, (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * Φ.t l
        ∈ (chart Γ (src p e)).integers := fun l => hint l
    have hres57 : ∀ l : Fin 2, (chart Γ (src p e)).residue ⟨_, hint'' l⟩
        = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ := fun l => rfl
    have hLI57 : LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : Fin 2 => (chart Γ (src p e)).residue ⟨_, hint'' l⟩) := by
      have : (fun l : Fin 2 => (chart Γ (src p e)).residue ⟨_, hint'' l⟩)
          = (fun l : Fin 2 => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := funext hres57
      rw [this]; exact hLI
    refine ⟨1, 1, Φ.t, fun i j => ?_, ⟨one_mul _, one_mul _⟩, hf1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq]; exact ⟨one_mem A, one_mem A⟩
      · rw [Matrix.one_apply_ne hij]; exact ⟨zero_mem A, zero_mem A⟩
    · refine ⟨hint'', fun l => by rw [hres57 l]; exact hLI.ne_zero l, fun l => ?_, hLI57⟩

      fin_cases l
      · show (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, hint'' 0⟩) = -((hasseExp Φ.toFamData 0 / w : ℕ) : ℤ)
        have h00 : hasseExp Φ.toFamData 0 = 0 := ModularCurve.MultCovering.hasseExp_zero Φ 0 rfl
        have hone : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData 0))⁻¹ * Φ.t 0 = 1 := by
          rw [h00, pow_zero, map_one, inv_one, Φ.t_zero 0 rfl]; exact one_mul _
        have : (chart Γ (src p e)).residue ⟨_, hint'' 0⟩ = 1 := by
          rw [res_congr (Γ := Γ) (src p e) (hint'' 0) (one_mem _) hone]; exact map_one _
        rw [this, h00]; simp
      · show (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 1, hint 1⟩) = -((hasseExp Φ.toFamData 1 / w : ℕ) : ℤ)
        rw [show (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 1, hint 1⟩
            = (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData 1, h0'⟩ from rfl, hsrc1, hn1, ← hw, Nat.div_self hwpos]
        simp
    · intro l
      exact ⟨hintI2 l, hneI l, fun hl => (hnode e).1 l hl⟩
    · obtain ⟨l, hl, hl1⟩ := (hnode e).2
      exact ⟨l, hl, hintI2 l, hl1⟩
    · intro l hl; exact Φ.t_zero l hl
    · intro R hR l hl
      exact ModularCurve.MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom p A hA Γ Δ Φ e R hR l hl
    · left
      exact ⟨1, le_rfl, ⟨hintI2 1, hord1⟩, by rw [hn1, hw]⟩

theorem ex_wideCert (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hAd : ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      LinearIndependent (IsLocalRing.ResidueField ↥A)
        (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    (∀ e, ∃ w : ℕ, 1 ≤ w ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          (((Δ.annIn e).modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) ∧
        (2 ≤ w →
          ∃ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar (1 * p)),
            (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) ∧ (Uinv * U = 1 ∧ U * Uinv = 1) ∧
            (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (U l j) * goodFamily Φ j) ∧
        (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * f l ∈ (chart Γ (src p e)).integers,
        (∀ l : Fin r, (chart Γ (src p e)).residue ⟨_, hint l⟩ ≠ 0) ∧
        (∀ l : Fin r, (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, hint l⟩) = -((hasseExp Φ.toFamData l / w : ℕ) : ℤ)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (chart Γ (src p e)).residue ⟨_, hint l⟩)) ∧
        (∀ l : Fin r, ∃ h : f l ∈ (chart Γ (tgt p e)).integers,
        (chart Γ (tgt p e)).residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩))) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩) = 1) ∧
        (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) ∧
        (∀ R ∈ (Δ.annIn e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
        ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f l, h⟩) = 1) ∧ hasseExp Φ.toFamData l = w) ∨
        (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ (chart Γ (tgt p e)).integers, (nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨f m₂, h⟩) = 1) ∧
        hasseExp Φ.toFamData m₁ < hasseExp Φ.toFamData m₂ ∧ hasseExp Φ.toFamData m₂ < w ∧ hasseExp Φ.toFamData m₁ + w ≤ 2 * hasseExp Φ.toFamData m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData m₁))⁻¹ * f m₁ ∈ (chart Γ (src p e)).integers) (c : IsLocalRing.ResidueField ↥A),
        (nodeSrc Γ e).ord ((chart Γ (src p e)).residue ⟨_, h⟩ - algebraMap (IsLocalRing.ResidueField ↥A) (Fbar A (src p e)) c) = 1))))) := by
  intro e
  obtain ⟨hint, hLI⟩ := hAd
  refine ⟨jWidth (ssValue Γ e), jWidth_pos _, ⟨1, one_mem A, by rw [inv_one]; exact one_mem A, ?_⟩, fun hw2 => ?_⟩
  · rw [mul_one, show (Δ.annIn e).modulus = ((p : ℕ) : ↥A) ^ jWidth (ssValue Γ e) from Δ.modulus_eq e]
    push_cast
    rfl
  · by_cases h13 : 13 ≤ p
    · exact wideCert_ge_thirteen p hp5 h13 A hA Γ Δ Φ s hs hint hLI e _ rfl hw2
    · exact wideCert_lt_thirteen p hp5 (lt_of_not_ge h13) A hA Γ Δ Φ s hs horthInf horthZero hint hLI e _ rfl hw2

theorem mainAllWithCert (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) :
    StatementAllWithCert p hp (1 * p) (dvd_mul_left p 1) := by
  intro r s hs
  obtain ⟨Φ, horthInf, horthZero, hAdapt⟩ :=
    ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue p hp5 s hs
  obtain ⟨A₀, hA₀⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
  letI : DecidableEq (IsLocalRing.ResidueField ↥A₀) := ModularCurve.instDecidableEqResidueFieldSemistable A₀
  haveI : CharP (IsLocalRing.ResidueField ↥A₀) p := charP_residueField p hp5 A₀ hA₀
  obtain ⟨Γ₀, -, -, ⟨Δ₀⟩⟩ := exists_rootCtx p hp5 A₀ hA₀
  refine ⟨nCharts, mAnnuli p, windowExp p s, modulusExp, compConst Φ s hs,
    goodFamily Φ, linkMatrix Φ s hs, linkMatrixInv Φ s hs, fun l => hasseExp Φ.toFamData l, linkBudget Φ s hs,
    mAnnuli_pos p hp hp5,
    goodFamily_zero_eq_one' p hp5 Φ s hs,
    ModularCurve.MultCovering.eq_sum_linkMatrix_mul_goodFamily Φ s hs,
    ModularCurve.MultCovering.linkMatrixInv_mul Φ s hs,
    ModularCurve.MultCovering.linkMatrix_mul_inv Φ s hs,
    hasseExp_zero' p hp5 Φ s hs,
    ModularCurve.MultCovering.one_le_hasseExp p A₀ hA₀ Γ₀ Φ,
    ModularCurve.MultCovering.hasseExp_le_modulusExp p A₀ hA₀ Γ₀ Δ₀ Φ,
    fun A hA inst => ?_⟩
  obtain rfl : inst = ModularCurve.instDecidableEqResidueFieldSemistable A := Subsingleton.elim _ _
  letI : DecidableEq (IsLocalRing.ResidueField ↥A) := ModularCurve.instDecidableEqResidueFieldSemistable A
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := charP_residueField p hp5 A hA
  obtain ⟨Γ, hsep, hcov, ⟨Δ⟩⟩ := exists_rootCtx p hp5 A hA
  exact ⟨Fbar A, fun i => inferInstance, fun i => inferInstance, chart Γ, Δ.annIn,
    Δ.annOut, src p, tgt p, nodeSrc Γ, nodeTgt Γ,
    fibreCoord p hp5 A hA Γ Δ, Δ.twoEnded, Δ.attached, node_is_end p hp5 A hA Γ Δ,
    end_unique p hp5 A hA Γ Δ, partition p hp5 A hA Γ Δ hsep hcov, gaussWindow p hp5 Φ s hs A hA Γ Δ,
    residueFields p hp5 A hA Γ Δ, connected p hp hp5, modulus_dvd' p hp5 A hA Γ Δ,
    p_dvd_modulus' p hp5 A hA Γ Δ, fibreCoords p hp5 A hA Γ Δ, chartComparison p hp5 Φ s hs A hA Γ Δ (hAdapt A hA Γ),
    crossComparison p hp5 Φ s hs A hA Γ Δ
      (fun P => (partition p hp5 A hA Γ Δ hsep hcov P).imp (fun h => ⟨h.choose, h.choose_spec.1⟩) (fun h => ⟨h.choose, h.choose_spec.1⟩)),
    linkBudget_spec Φ s hs A hA,
    ex_infEnds p hp5 A hA Γ Δ Φ s hs,
    ex_infEnds_one p hp5 A hA Γ Δ Φ s hs,
    ex_zeroEnds p hp5 A hA Γ Δ Φ s hs,
    ex_tubeSmall p hp5 A hA Γ Δ Φ s hs,
    ex_wideCert p hp5 A hA Γ Δ Φ s hs horthInf horthZero (hAdapt A hA Γ),
    ex_tieWith p hp5 A hA Γ Δ hp (dvd_mul_left p 1)⟩

end ModularCurve.MultCovering

namespace ModularCurve p2m_export "ModularCurve" "embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar qExpand jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full modularFunctionFieldBar coeffMap coeffEmb coeffEmb_mem_laurentBaseChange ssJSet PlaceSpecialization.LevelOneProlongationPair instDecidableEqResidueFieldSemistable jqModC modularFunctionFieldC PlaceSpecialization frobOnPlacesGeomLevel frobNodePair ratFuncEquivCharLOneC charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar PlaceSpecialization.LevelOneProlongationPair.mem_chartFst_nodes_iff ssPlaces IsAffineGeomPlace MultCovering.AnnCtx jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne jWidth_pos jWidth_eq_one_or hasPrincipalDivisors_modularFunctionFieldC_of_perfectField ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue MultCovering.zeroChart_chartData_goodFamilyZero_of_linearIndependent MultCovering.zeroChart_chartData_goodFamilyZero_of_lt_thirteen MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom MultCovering.jF_mem_infChart_integers MultCovering.jpF_mem_infChart_integers MultCovering.infChart_residue_jF MultCovering.infChart_residue_jpF MultCovering.mem_infChart_integers_iff_coe_mem_modularLocalized MultCovering.infChart_residue_eq_modularRedLocHom MultCovering.infChart_residue_coeffMap MultCovering.mem_infChart_integers_of_forall_coeff_mem MultCovering.infChart_mem_integers_residue_ne_zero_of_qCoeff MultCovering.mem_infChart_integers_iff MultCovering.infChart_residue_ne_zero_iff_exists_quotient MultCovering.not_isSSCentred_of_mem_infChart_dom MultCovering.mem_zeroChart_nodes_iff MultCovering.not_isSSCentred_of_mem_zeroChart_dom MultCovering.cuspInftyBar_mem_infChart_dom MultCovering.AnnCtx.exists_mem_pow_modulusExp_eq_modulus_mul MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne MultCovering.linkMatrixInv_mul MultCovering.linkMatrix_mul_inv MultCovering.AnnCtx.exists_mem_modulus_eq_mul MultCovering.AnnCtx.exists_isUnit_modulus_eq_mul_of_ssValue_ne MultCovering.infChart_chartData MultCovering.hasseExp_zero MultCovering.one_le_hasseExp MultCovering.zeroChart_residue_goodFamilyZero_ne_zero exists_uniform_window_smul_mem_integers_of_qCoeff_criterion PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord MultCovering.hasseExp_le_modulusExp MultCovering.infChart_chartData_goodFamily MultCovering.exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos MultCovering.eq_sum_linkMatrix_mul_goodFamily MultCovering.linkBudget_spec MultCovering.neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero MultCovering.residue_evalAt_goodFamilyZero_div_eq_evalAt_nodeSrc_of_forall_widthOne MultCovering.zeroChart_chartData_goodFamilyZero_of_forall_ssValue_ne MultCovering.evalAt_goodFamily_mem_maximalIdeal_of_mem_annIn_dom MultCovering.chartComparison_infChart_of_fibreCoord MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord isCurveOver_modularFunctionFieldBar MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom MultCovering.exists_unimodular_famData_wideCertificates MultCovering.exists_unimodular_famData_ord_nodeSrc_zeroChart_residue_eq_neg_hasseExp_div_jWidth_of_eq_eleven MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.hasseExp_eq_jWidth_of_genus_zero MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.eq_mAnnuli_add_one_of_isEmbBasis" end ModularCurve
p2m_open_scoped "ModularCurve" in
open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.ModularCurve.MultCovering in
theorem ModularCurve.exists_uniform_multCovering_structure_tied_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∃ (n m B k : ℕ) (Cc : ℝ), 0 < m ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar N) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar N)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar N),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar N ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩))) := by
  have hNp : N = p := ((Nat.prime_dvd_prime_iff_eq hp hN).mp hpN).symm
  subst hNp
  haveI : Fact N.Prime := ⟨hp⟩
  first
  | exact StatementAll_congr N hp (one_mul N) (dvd_mul_left N 1) hpN (mainAll N hp hN5) s hs

p2m_open_scoped "ModularCurve" in
open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.ModularCurve.MultCovering in

theorem ModularCurve.exists_uniform_multCovering_with_goodFamily_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∃ (n m B k : ℕ) (Cc : ℝ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ), 0 < m ∧
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) ∧
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) ∧
    Minv * M = 1 ∧ M * Minv = 1 ∧
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) ∧ (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) ∧ (∀ l, nexp l ≤ k) ∧
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar N) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar N)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar N),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar N ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) ∧
      (∀ e, ∀ l : Fin r, ∃ h : t l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩))) ∧
      (∀ e, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩) = 1) ∧
      (∀ e, ∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l
          ∈ (C (src e)).integers, (C (src e)).residue ⟨_, h⟩ ≠ 0) ∧
      (∀ e, ∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        t l ∈ R.toValuationSubring ∧ ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)) ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u)) := by
  have hNp : N = p := ((Nat.prime_dvd_prime_iff_eq hp hN).mp hpN).symm
  subst hNp
  haveI : Fact N.Prime := ⟨hp⟩
  exact StatementAllWith_congr N hp (one_mul N) (dvd_mul_left N 1) hpN (mainAllWith N hp hN5) s hs

p2m_open "ModularCurve~jBar" in open _root_.P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.ModularCurve _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.ModularCurve.MultCovering in
set_option maxHeartbeats 3200000 in

theorem solution (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∃ (n m B k : ℕ) (Cc : ℝ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ), 0 < m ∧
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) ∧
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) ∧
    Minv * M = 1 ∧ M * Minv = 1 ∧
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) ∧ (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) ∧ (∀ l, nexp l ≤ k) ∧
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar N) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar N)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar N),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar N ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) ∧
      (∀ e, ∀ l : Fin r, ∃ h : t l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩))) ∧
      (∀ e, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩) = 1) ∧
      (∀ e, ∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l
          ∈ (C (src e)).integers, (C (src e)).residue ⟨_, h⟩ ≠ 0) ∧
      (∀ e, ∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        t l ∈ R.toValuationSubring ∧ ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
      (∀ e, ∃ w : ℕ, 1 ≤ w ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          (((An e).modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) ∧
        (2 ≤ w →
          ∃ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar N),
            (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) ∧ (Uinv * U = 1 ∧ U * Uinv = 1) ∧
            (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (U l j) * t j) ∧
        (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * f l ∈ (C (src e)).integers,
        (∀ l : Fin r, (C (src e)).residue ⟨_, hint l⟩ ≠ 0) ∧
        (∀ l : Fin r, (xs e).ord ((C (src e)).residue ⟨_, hint l⟩) = -((nexp l / w : ℕ) : ℤ)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (C (src e)).residue ⟨_, hint l⟩)) ∧
        (∀ l : Fin r, ∃ h : f l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩))) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩) = 1) ∧
        (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) ∧
        (∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
        ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩) = 1) ∧ nexp l = w) ∨
        (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f m₂, h⟩) = 1) ∧
        nexp m₁ < nexp m₂ ∧ nexp m₂ < w ∧ nexp m₁ + w ≤ 2 * nexp m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp m₁))⁻¹ * f m₁ ∈ (C (src e)).integers) (c : IsLocalRing.ResidueField ↥A),
        (xs e).ord ((C (src e)).residue ⟨_, h⟩ - algebraMap (IsLocalRing.ResidueField ↥A) (Fbar (src e)) c) = 1))))) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)) ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u)) := by
  have hNp : N = p := ((Nat.prime_dvd_prime_iff_eq hp hN).mp hpN).symm
  subst hNp
  haveI : Fact N.Prime := ⟨hp⟩
  exact StatementAllWithCert_congr N hp (one_mul N) (dvd_mul_left N 1) hpN (mainAllWithCert N hp hN5) s hs

end S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le (solution)
