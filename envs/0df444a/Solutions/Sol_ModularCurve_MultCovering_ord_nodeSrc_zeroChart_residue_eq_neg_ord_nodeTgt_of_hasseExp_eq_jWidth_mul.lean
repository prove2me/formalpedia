-- Prove2me | solution 1 for ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c3d48647-d571-5445-b16f-39a116f81c9a

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal
import Theorems.Thm_ModularCurve_MultCovering_exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_exists_combination_hasseExp_two_eq_prod_widthOne
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_ModularCurve_zero_mem_ssJSetHasse_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSetHasse_iff
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_forall_ord_nonneg
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase"
p2m_attr_erase "instance" "instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 3200000

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange ssJSet PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldC PlaceSpecialization charLGeomPlaceEquiv charLGeomPlaceOfPoint CharPReduction.integralCoeffs CharPReduction.coeffRed_coeff CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar cuspZeroBar_def jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne jWidth_eq_ite jWidth_pos jWidth_eq_one_or ord_charLGeomPlaceEquiv_placeInfty_jqModC eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty zero_mem_ssJSetHasse_iff ssJSetHasse ofNat1728_mem_ssJSetHasse_iff ssJSet_eq_ssJSetHasse exists_eq_algebraMap_of_forall_ord_nonneg hasPrincipalDivisors_modularFunctionFieldBar_unconditional coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem ssJSet_nonempty ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar CharPReduction.modularRedLocHom_eq_coeffRed ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "FamData zeroSeries coe_frickeInvolutionBar_t hasseContent hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq nodeSrc nodeTgt AnnCtx cuspZeroBar_not_mem_infChart_dom infChart_residue_eq_ssPolyBar_mul_of_orthogonal exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul eq_mAnnuli_add_one_of_isEmbBasis mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge hasseExp_le_two_of_thirteen_le mem_zeroChart_nodes_iff infChart_residue_goodFamily exists_combination_hasseExp_two_eq_prod_widthOne infChart_nodeData_exists_node_of_member infChart_goodFamily_residue_ne_zero"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

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

private theorem _root_.ModularCurve.MultCovering.t_ne_zero (l : Fin r) : Φ.t l ≠ 0 := Φ.t_basis.1.ne_zero l

p2m_export "ModularCurve.MultCovering" "t_ne_zero"
private theorem _root_.ModularCurve.MultCovering.t_mem_riemannRochSpace (l : Fin r) : Φ.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← Φ.t_basis.2]
  exact Submodule.subset_span ⟨l, rfl⟩

p2m_export "ModularCurve.MultCovering" "t_mem_riemannRochSpace"
private theorem _root_.ModularCurve.MultCovering.t_pole (l : Fin r) :
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

p2m_export "ModularCurve.MultCovering" "t_pole"
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

private theorem _root_.ModularCurve.MultCovering.zeroChart_residue_goodFamilyZero_ne_zero :
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

p2m_export "ModularCurve.MultCovering" "zeroChart_residue_goodFamilyZero_ne_zero"
include hA in

private theorem _root_.ModularCurve.MultCovering.goodFamilyZero_mem_zeroChart_integers : ∀ l : Fin r, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers :=
  (zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ).1

p2m_export "ModularCurve.MultCovering" "goodFamilyZero_mem_zeroChart_integers"
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

section Bound

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA in

theorem exists_mem_dom_evalAt_eq_root (e : Fin (mAnnuli p)) (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : AlgebraicClosure ℚ, c ^ m = (p : AlgebraicClosure ℚ) ∧ c ∈ A ∧
      ∃ Q ∈ (Δ.annOut e).dom, Q.evalAt (Δ.annOut e).param = c := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure ℚ) (by omega : 0 < m)
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hc; exact hp0 hc.symm
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p

  have hcA : c ∈ A := by
    by_contra h
    have hinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left h
    have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
    have hone : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) * (⟨c⁻¹, hinv⟩ : ↥A) ^ m = 1 := by
      apply Subtype.ext
      show (p : AlgebraicClosure ℚ) * (c⁻¹) ^ m = 1
      rw [← hc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hc0)]
    have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← hone]; exact Ideal.mul_mem_right _ _ hp𝔪
    exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  set cA : ↥A := ⟨c, hcA⟩ with hcA_def
  have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
  have hcApow : cA ^ m = ⟨(p : AlgebraicClosure ℚ), hpA⟩ := Subtype.ext (by simpa [hcA_def] using hc)
  have hc𝔪 : cA ∈ IsLocalRing.maximalIdeal ↥A :=
    (IsLocalRing.maximalIdeal.isMaximal ↥A).isPrime.mem_of_pow_mem m (by rw [hcApow]; exact hp𝔪)

  have hmod : (Δ.annOut e).modulus = ((p : ℕ) : ↥A) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_eq e
  have hw : 1 ≤ jWidth (ssValue Γ e) := jWidth_pos _
  have hpnat : ((p : ℕ) : ↥A) = ⟨(p : AlgebraicClosure ℚ), hpA⟩ := Subtype.ext (by simp)
  have hdiv : ∃ m' ∈ IsLocalRing.maximalIdeal ↥A, ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = c * m' := by
    refine ⟨cA ^ (m * jWidth (ssValue Γ e) - 1), ?_, ?_⟩
    · have h2 : 2 ≤ m * jWidth (ssValue Γ e) := le_trans (by omega) (Nat.mul_le_mul hm hw)
      exact Ideal.pow_mem_of_mem _ hc𝔪 _ (by omega)
    · rw [hmod, hpnat, ← hcApow, ← pow_mul]
      have : m * jWidth (ssValue Γ e) = (m * jWidth (ssValue Γ e) - 1) + 1 := by
        have : 1 ≤ m * jWidth (ssValue Γ e) := le_trans (by omega) (Nat.mul_le_mul (by omega : 1 ≤ m) hw)
        omega
      conv_lhs => rw [this, pow_succ]
      push_cast
      ring
  obtain ⟨Q, ⟨hQ, hQc⟩, -⟩ := (Δ.annOut e).existsUnique_evalAt_eq cA hc𝔪 (by exact hc0) hdiv
  exact ⟨c, hc, hcA, Q, hQ, hQc⟩

include hA in

theorem annOut_wide (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμp : μ (p : AlgebraicClosure ℚ) < 1)
    (e : Fin (mAnnuli p)) :
    ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
      μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  obtain ⟨c₁, hc₁, -, Q₁, hQ₁, hQ₁c⟩ := exists_mem_dom_evalAt_eq_root p A hA Γ Δ e 2 le_rfl
  obtain ⟨c₂, hc₂, -, Q₂, hQ₂, hQ₂c⟩ := exists_mem_dom_evalAt_eq_root p A hA Γ Δ e 4 (by norm_num)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁c, hQ₂c]
  intro h
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h1 : μ c₁ ^ 4 = μ (p : AlgebraicClosure ℚ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← map_pow, hc₁]
  have h2 : μ c₂ ^ 4 = μ (p : AlgebraicClosure ℚ) := by rw [← map_pow, hc₂]
  rw [h] at h1
  rw [h1] at h2

  nlinarith

include hA Γ Δ in

theorem hasseExp_le_modulusExp : ∀ l : Fin r, hasseExp Φ.toFamData l ≤ modulusExp := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  intro l
  rw [show modulusExp = 3 from rfl]
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl]; omega
  have hl1 : 1 ≤ (l : ℕ) := by omega
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint, hnode⟩ := infChart_nodeData_exists_node_of_member p A hA Γ Φ
  obtain ⟨e, he1⟩ := hnode l hl1
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  set n := hasseExp Φ.toFamData l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e

  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (Φ.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := t_pole p Φ l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (Φ.t l) (hint l) (hres_ne l) ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    (hint0 l) (hres0 l) hpole
  rw [he1, zpow_one] at hb

  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  rw [hmodval, map_pow, map_pow] at hb
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hnw : n ≤ jWidth (ssValue Γ e) := (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp hb
  rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h <;> omega

end Bound

section WidthOne

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA Δ in

theorem twoEnd_bounds (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμp : μ (p : AlgebraicClosure ℚ) < 1)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (hres : ∀ l, (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩ ≠ 0)
    (hint0 : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hres0 : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩ ≠ 0)
    (e : Fin (mAnnuli p)) (l : Fin r) :
    (μ (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e)) ^ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩)
        ≤ μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l ∧
      μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l *
        (μ (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e))
          ^ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩) ≤ 1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set n := hasseExp Φ.toFamData l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (Φ.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := t_pole p Φ l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (Φ.t l) (hint l) (hres l) ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    (hint0 l) (hres0 l) hpole
  have hb' := AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (Φ.t l) (hint l) (hres l) ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    (hint0 l) (hres0 l) hpole
  rw [hmodval, map_pow, map_pow] at hb hb'
  exact ⟨hb, hb'⟩

include hA Δ in

theorem exists_node_hasseExp_le_jWidth : ∀ l : Fin r, 1 ≤ (l : ℕ) → ∃ e : Fin (mAnnuli p),
    hasseExp Φ.toFamData l ≤ jWidth (ssValue Γ e) := by
  intro l hl1
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint, hnode⟩ := infChart_nodeData_exists_node_of_member p A hA Γ Φ
  obtain ⟨e, he1⟩ := hnode l hl1
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hb, -⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint hres_ne hint0 hres0 e l
  refine ⟨e, ?_⟩
  rw [he1, zpow_one] at hb
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp hb

include hA Δ in

theorem hasseExp_le_one_of_forall_widthOne (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∀ l : Fin r, hasseExp Φ.toFamData l ≤ 1 := by
  intro l
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl]; omega
  obtain ⟨e, he⟩ := exists_node_hasseExp_le_jWidth p A hA Γ Δ Φ l (by omega)
  rw [jWidth_of_ne (hw e).1 (hw e).2] at he
  exact he

include hA Δ in

theorem neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  refine ⟨hint0, fun e l => ?_⟩
  obtain ⟨-, hb'⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint2 hres_ne hint0 hres0 e l
  have hn1 := hasseExp_le_one_of_forall_widthOne p A hA Γ Δ Φ hw l
  rw [jWidth_of_ne (hw e).1 (hw e).2, pow_one] at hb'
  set a' := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩) with ha'
  set n := hasseExp Φ.toFamData l with hn
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

  have hz : μ (p : AlgebraicClosure ℚ) ^ ((n : ℤ) + a') ≤ 1 := by
    rw [zpow_add₀ hμp0.ne', zpow_natCast]; exact hb'
  have h0 : 0 ≤ (n : ℤ) + a' := (zpow_le_one_iff_right_of_lt_one₀ hμp0 hμp).mp hz
  omega

include hA in

theorem zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (l : Fin r) (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)),
        v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  refine ⟨hint0, fun l v hv => ?_⟩
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero _).mpr (pow_ne_zero _ hp0))
  have hg0 : goodFamilyZero Φ.toFamData l ≠ 0 := mul_ne_zero hx0 (t_ne_zero p Φ l)
  apply AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
    (zeroChart Γ) (goodFamilyZero Φ.toFamData l) hg0 (hint0 l) (hres0 l) _ v hv

  intro P hP
  have hord : P.ord (goodFamilyZero Φ.toFamData l) = P.ord (Φ.t l) := by
    show P.ord (_ * Φ.t l) = _
    rw [P.ord_mul hx0 (t_ne_zero p Φ l), Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
  rw [hord]
  by_contra hneg
  push_neg at hneg
  obtain rfl := t_pole p Φ l P hneg

  apply cuspZeroBar_not_mem_infChart_dom' p A Γ
  have hP' : frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p) ∈ (infChart Γ).dom :=
    (ComponentChart.mem_comap_dom (frickeInvolutionBar (1 * p)) (infChart Γ) _).mp hP
  rw [cuspZeroBar_def]
  exact hP'

include hA Δ in

theorem neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ)
          ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  refine ⟨hint0, fun e l => ?_⟩
  obtain ⟨-, hb'⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint2 hres_ne hint0 hres0 e l
  set a' := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩) with ha'
  set n := hasseExp Φ.toFamData l with hn
  set w := jWidth (ssValue Γ e) with hw_def
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hz : μ (p : AlgebraicClosure ℚ) ^ ((n : ℤ) + (w : ℤ) * a') ≤ 1 := by
    rw [zpow_add₀ hμp0.ne', zpow_mul, zpow_natCast, zpow_natCast]; exact hb'
  have h0 : 0 ≤ (n : ℤ) + (w : ℤ) * a' := (zpow_le_one_iff_right_of_lt_one₀ hμp0 hμp).mp hz
  have hw0 : 0 < w := jWidth_pos (ssValue Γ e)
  have hdm : w * (n / w) + n % w = n := Nat.div_add_mod n w
  have hml : n % w < w := Nat.mod_lt n hw0
  by_contra hlt
  push_neg at hlt
  have hle : a' ≤ -((n / w : ℕ) : ℤ) - 1 := by omega
  have hmul : (w : ℤ) * a' ≤ (w : ℤ) * (-((n / w : ℕ) : ℤ) - 1) :=
    mul_le_mul_of_nonneg_left hle (by exact_mod_cast hw0.le)
  have hq : (w : ℤ) * ((n / w : ℕ) : ℤ) + ((n % w : ℕ) : ℤ) = (n : ℤ) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) hdm
    simpa only [Nat.cast_add, Nat.cast_mul] using this
  have hml' : ((n % w : ℕ) : ℤ) < (w : ℤ) := by exact_mod_cast hml
  linarith

end WidthOne

section Orth

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)

theorem coe_sum_single_smul_coeff (X : Fin r → ↥(modularFunctionFieldFull (1 * p))) (l : Fin r) (a : ℚ) (m : ℤ) :
    (((∑ i, (Pi.single l a : Fin r → ℚ) i • X i : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m
      = a * ((X l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
  rw [Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => (h (Finset.mem_univ l)).elim), Pi.single_eq_same]
  first
  | rfl
  | (rw [IntermediateField.coe_smul]; rfl)
  | simp [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul]

namespace FamData p2m_export "ModularCurve.MultCovering.FamData" "t t_eq tRat" end FamData
p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.t_ne_zero (hbasis : IsEmbBasis (1 * p) D.t) (l : Fin r) : D.t l ≠ 0 := hbasis.1.ne_zero l

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.t_mem_riemannRochSpace (hbasis : IsEmbBasis (1 * p) D.t) (l : Fin r) :
    D.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← hbasis.2]; exact Submodule.subset_span ⟨l, rfl⟩

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.t_pole (hbasis : IsEmbBasis (1 * p) D.t) (l : Fin r) :
    ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (D.t l) < 0 → W = cuspInftyBar (1 * p) := by
  intro W hW
  by_contra hne
  rcases (mem_riemannRochSpace_iff.mp (FamData.t_mem_riemannRochSpace p D hbasis l)) W with h | h
  · exact FamData.t_ne_zero p D hbasis l h
  · have : (embDivisor (1 * p)) W = 0 := by
      show ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) W = 0
      rw [Finsupp.smul_apply]
      first
      | rw [Finsupp.single_eq_of_ne hne, smul_zero]
      | rw [Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]
    rw [this, neg_zero] at h
    omega

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.exists_isContent_of_isEmbBasis (hbasis : IsEmbBasis (1 * p) D.t)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (l : Fin r) : ∃ n : ℤ, IsContent D l n := by
  obtain ⟨c, hc0, hcA⟩ := exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar p
    (embDegree (1 * p)) (D.t l) (FamData.t_mem_riemannRochSpace p D hbasis l) (FamData.t_ne_zero p D hbasis l) A hA
  exact exists_isContent D l (FamData.t_ne_zero p D hbasis l) A hA c hc0 hcA

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.hasseContent_nonneg_of_orth (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (l : Fin r) : 0 ≤ hasseContent D l := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  have hn := isContent_hasseContent D l (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l)
  obtain ⟨k₀, hk₀, hk₀n⟩ := hn.2
  have key := (horthZero (Pi.single l 1)).mpr (fun i => by
    by_cases hi : i = l
    · subst hi; rw [Pi.single_eq_same, padicValRat.one]; omega
    · rw [Pi.single_eq_of_ne hi, padicValRat.zero]; omega) k₀
  rw [coe_sum_single_smul_coeff, one_mul] at key
  rw [← hk₀n]
  exact key

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∃ hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers,
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ ≠ 0 := by
  have key : ∀ l, ∃ h : goodFamilyZero D l ∈ (zeroChart Γ).integers, (zeroChart Γ).residue ⟨goodFamilyZero D l, h⟩ ≠ 0 := by
    intro l
    obtain ⟨hf, k, hu⟩ := frickeInvolutionBar_goodFamilyZero_qCoeff D l
      (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l) (FamData.hasseContent_nonneg_of_orth p D hbasis horthZero l) A hA
    obtain ⟨h, hres⟩ := infChart_criterion p A Γ _ hf ⟨k, hu⟩
    refine ⟨h, ?_⟩
    show ((infChart Γ).comap (frickeInvolutionBar (1 * p))).residue ⟨goodFamilyZero D l, h⟩ ≠ 0
    rw [ComponentChart.comap_residue_apply]
    exact hres
  exact ⟨fun l => (key l).1, fun l => (key l).2⟩

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.goodFamilyZero_mem_zeroChart_integers (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers :=
  (FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ).1

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.zeroChart_residue_goodFamilyZero_ne_zero (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ ≠ 0 := by
  obtain ⟨h, hne⟩ := FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ
  exact hne

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ (l : Fin r) (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hres0 := FamData.zeroChart_residue_goodFamilyZero_ne_zero p D hbasis horthZero A hA Γ hint
  intro l v hv
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp D l))⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero _).mpr (pow_ne_zero _ hp0))
  have hg0 : goodFamilyZero D l ≠ 0 := mul_ne_zero hx0 (FamData.t_ne_zero p D hbasis l)
  apply AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
    (zeroChart Γ) (goodFamilyZero D l) hg0 (hint l) (hres0 l) _ v hv
  intro P hP
  have hord : P.ord (goodFamilyZero D l) = P.ord (D.t l) := by
    show P.ord (_ * D.t l) = _
    rw [P.ord_mul hx0 (FamData.t_ne_zero p D hbasis l), Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
  rw [hord]
  by_contra hneg
  push_neg at hneg
  obtain rfl := FamData.t_pole p D hbasis l P hneg
  apply cuspZeroBar_not_mem_infChart_dom' p A Γ
  have hP' : frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p) ∈ (infChart Γ).dom :=
    (ComponentChart.mem_comap_dom (frickeInvolutionBar (1 * p)) (infChart Γ) _).mp hP
  rw [cuspZeroBar_def]
  exact hP'

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.exists_infChart_residue_t_ne_zero_of_orthInf
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (l : Fin r) :
    ∃ h : D.t l ∈ (infChart Γ).integers, (infChart Γ).residue ⟨D.t l, h⟩ ≠ 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set g : LaurentSeries ℚ := ((D.tRat l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) with hg

  have hle : ∀ k : ℤ, g.coeff k ≠ 0 → (0 : ℤ) ≤ padicValRat p (g.coeff k) := by
    intro k _
    have key := (horthInf (Pi.single l 1)).mpr (fun i => by
      by_cases hi : i = l
      · subst hi; rw [Pi.single_eq_same, padicValRat.one]
      · rw [Pi.single_eq_of_ne hi, padicValRat.zero]) k
    rw [coe_sum_single_smul_coeff, one_mul] at key
    exact key

  have hnot : ¬ ∀ i, (0 : ℤ) ≤ padicValRat p ((Pi.single l ((p : ℚ)⁻¹) : Fin r → ℚ) i) := by
    intro h
    have := h l
    rw [Pi.single_eq_same, padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt] at this
    omega
  rw [← horthInf] at hnot
  push_neg at hnot
  obtain ⟨m, hm⟩ := hnot
  rw [coe_sum_single_smul_coeff] at hm
  have hm0 : g.coeff m ≠ 0 := by
    intro h0; rw [← hg, h0, mul_zero, padicValRat.zero] at hm; exact lt_irrefl _ hm
  have hv0 : padicValRat p (g.coeff m) = 0 := by
    rw [← hg, padicValRat.mul (inv_ne_zero hp0) hm0, padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt] at hm
    have := hle m hm0
    omega
  obtain ⟨h1, h2⟩ := coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat A (Fact.out : p.Prime) hA g 0
    (fun k hk => by exact_mod_cast hle k hk) m hm0 (by rw [hv0]; try rfl)
  have hsm : ((p : ℚ) ^ (0 : ℤ))⁻¹ • g = g := by rw [zpow_zero, inv_one, one_smul]
  rw [hsm] at h1 h2
  have hcoe : ((D.t l : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g := by
    rw [D.t_eq l]
  have hf : ∀ k : ℤ, ((D.t l : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by
    intro k; rw [hcoe]; exact h1 k
  refine infChart_criterion p A Γ (D.t l) hf ⟨m, ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff]
  refine le_antisymm (A.valuation_le_one _) ?_
  have h3 : ¬ A.valuation ((coeffEmb (AlgebraicClosure ℚ) g).coeff m) < 1 :=
    fun h => h2 ((ValuationSubring.mem_nonunits_iff A).mpr h)
  rw [not_lt, ← hcoe] at h3
  exact h3

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.neg_one_le_ord_nodeSrc_residue_goodFamilyZero (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hle1 : ∀ l : Fin r, hasseExp D l ≤ 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ (e : Fin (mAnnuli p)) (l : Fin r), -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  intro e l
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hC, hres⟩ := FamData.exists_infChart_residue_t_ne_zero_of_orthInf p D horthInf A hA Γ l
  have hres0 := FamData.zeroChart_residue_goodFamilyZero_ne_zero p D hbasis horthZero A hA Γ hint
  set n := hasseExp D l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (D.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := FamData.t_pole p D hbasis l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hb' := AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (D.t l) hC hres ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA (hint l) (hres0 l) hpole
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  rw [hmodval, map_pow, map_pow] at hb'
  set a' := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) with ha'
  set w := jWidth (ssValue Γ e) with hw_def
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hz : μ (p : AlgebraicClosure ℚ) ^ ((n : ℤ) + (w : ℤ) * a') ≤ 1 := by
    rw [zpow_add₀ hμp0.ne', zpow_mul, zpow_natCast, zpow_natCast]; exact hb'
  have h0 : 0 ≤ (n : ℤ) + (w : ℤ) * a' := (zpow_le_one_iff_right_of_lt_one₀ hμp0 hμp).mp hz
  have hw1 : (1 : ℤ) ≤ w := by exact_mod_cast jWidth_pos (ssValue Γ e)
  have hn1 : (n : ℤ) ≤ 1 := by exact_mod_cast hle1 l
  by_contra hlt
  push_neg at hlt
  have : (w : ℤ) * a' ≤ a' := by nlinarith
  omega

end Orth

section OrthOne

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.tRat_eq_one_of_t_eq_one (l : Fin r) (h : D.t l = 1) : D.tRat l = 1 := by
  have h2 : coeffEmb (AlgebraicClosure ℚ) (D.tRat l : LaurentSeries ℚ) = 1 := by
    have := congrArg Subtype.val (D.t_eq l)
    rw [h] at this
    exact this.symm
  exact Subtype.ext ((coeffEmb (AlgebraicClosure ℚ)).injective (by rw [h2, OneMemClass.coe_one, map_one]))

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.one_le_hasseExp_of_orth
    (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp D l := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  intro l hl
  by_contra hlt
  push_neg at hlt
  have h0n : hasseExp D l = 0 := by omega
  have hp : (p : ℕ).Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA

  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) l.2
  set l₀ : Fin r := ⟨0, hr⟩ with hl₀
  have hl0 : (l₀ : ℕ) = 0 := rfl
  have hll₀ : l ≠ l₀ := by intro h; rw [h, hl0] at hl; omega
  have ht0 : D.tRat l₀ = 1 := FamData.tRat_eq_one_of_t_eq_one p D l₀ (hzero l₀ hl0)

  obtain ⟨hint, hres0⟩ := FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ
  have hg : goodFamilyZero D l = D.t l := by
    show (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp D l))⁻¹ * D.t l = D.t l
    rw [h0n, pow_zero, map_one, inv_one, one_mul (D.t l)]
  have hunit : ∃ h : frickeInvolutionBar (1 * p) (D.t l) ∈ (infChart Γ).integers, (infChart Γ).residue ⟨_, h⟩ ≠ 0 := by
    have e1 : frickeInvolutionBar (1 * p) (goodFamilyZero D l) = frickeInvolutionBar (1 * p) (D.t l) := by rw [hg]
    have key : ∃ h : frickeInvolutionBar (1 * p) (goodFamilyZero D l) ∈ (infChart Γ).integers,
        (infChart Γ).residue ⟨_, h⟩ ≠ 0 := by
      refine ⟨hint l, ?_⟩
      have := hres0 l
      rwa [show (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩
        = (infChart Γ).residue ⟨frickeInvolutionBar (1 * p) (goodFamilyZero D l), hint l⟩ from
          ComponentChart.comap_residue_apply _ _ _] at this
    rw [e1] at key
    exact key
  obtain ⟨hwf_int, hwf_res⟩ := hunit

  obtain ⟨hf_int, -⟩ := FamData.exists_infChart_residue_t_ne_zero_of_orthInf p D horthInf A hA Γ l

  obtain ⟨c₀, hc₀, hconst⟩ :=
    ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar A hA (infChart Γ)
      (infChart_mem_integers_iff p A Γ) (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
      (cuspZeroBar_not_mem_infChart_dom' p A Γ) (D.t l) (FamData.t_ne_zero p D hbasis l) (FamData.t_pole p D hbasis l)
      hf_int hwf_int hwf_res

  set b : ℤ → ℚ := fun m => (zeroSeries D l).coeff m with hb
  have hcontent := isContent_hasseContent D l (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l)
  have hc0 : hasseContent D l = 0 := by
    have h1 := hasseExp_cast D l (FamData.hasseContent_nonneg_of_orth p D hbasis horthZero l)
    rw [h0n] at h1; exact_mod_cast h1.symm
  have hbint : ∀ m, b m ≠ 0 → 0 ≤ padicValRat p (b m) := by
    intro m hm; have := hcontent.1 m hm; rw [hc0] at this; exact this
  have hbA : ∀ m, ((b m : ℚ) : AlgebraicClosure ℚ) ∈ A := by
    intro m
    by_cases hm : b m = 0
    · rw [hm, Rat.cast_zero]; exact zero_mem A
    · exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hm).mpr (hbint m hm)
  have hcoeff : ∀ m, ((frickeInvolutionBar (1 * p) (D.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff m = ((b m : ℚ) : AlgebraicClosure ℚ) := by
    intro m; rw [coe_frickeInvolutionBar_t, coeffEmb_coeff, eq_ratCast]

  have h₂ : ((frickeInvolutionBar (1 * p) (D.t l) : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A) :=
    (infChart_mem_integers_iff p A Γ _).mp hwf_int
  obtain ⟨hwf_int', hres₂⟩ := infChart_residue_eq_modularRedLocHom' p A Γ _ h₂
  have hint_coeffs : ((frickeInvolutionBar (1 * p) (D.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring := fun m => by
    rw [hcoeff]; exact hbA m
  have hred : ∀ m : ℤ, IsLocalRing.residue ↥A ⟨((b m : ℚ) : AlgebraicClosure ℚ), hbA m⟩
      = (HahnSeries.single (0 : ℤ) c₀ : LaurentSeries (ResidueField ↥A)).coeff m := by
    intro m
    have e2 := hres₂
    rw [hconst, CharPReduction.modularRedLocHom_eq_coeffRed _ _ _ _ hint_coeffs] at e2

    have e3 := congrArg (fun z : LaurentSeries (ResidueField ↥A) => z.coeff m) e2
    simp only [CharPReduction.coeffRed_coeff] at e3
    rw [← algebraMap_laurentSeries_eq_single]
    convert e3.symm using 1
    all_goals first | rfl | simp only [hcoeff] | (congr 1; first | rfl | simp only [hcoeff])

  have hbpos : ∀ m, m ≠ 0 → b m ≠ 0 → 1 ≤ padicValRat p (b m) := by
    intro m hm hbm
    have h1 : IsLocalRing.residue ↥A ⟨((b m : ℚ) : AlgebraicClosure ℚ), hbA m⟩ = 0 := by
      rw [hred m, HahnSeries.coeff_single_of_ne hm]
    rw [IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff] at h1
    have h2 : padicValRat p (b m) ≠ 0 := fun h =>
      (lt_irrefl _) (h1.trans_le ((ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero A hp hAp hbm).mpr h).ge)
    have := hbint m hbm
    omega

  set cv : Fin r → ℚ := Pi.single l ((p : ℚ)⁻¹) - Pi.single l₀ ((p : ℚ)⁻¹ * b 0) with hcv
  have hsum : ∀ m : ℤ, (((∑ i, cv i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p)))) :
      LaurentSeries ℚ).coeff m = (p : ℚ)⁻¹ * b m - (p : ℚ)⁻¹ * b 0 * ((1 : LaurentSeries ℚ).coeff m) := by
    intro m
    have : (∑ i, cv i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p)))
        = (∑ i, (Pi.single l ((p : ℚ)⁻¹) : Fin r → ℚ) i • frickeInvolutionFull (1 * p) (D.tRat i))
          - ∑ i, (Pi.single l₀ ((p : ℚ)⁻¹ * b 0) : Fin r → ℚ) i • frickeInvolutionFull (1 * p) (D.tRat i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcv, Pi.sub_apply, sub_smul]
    rw [this, AddSubgroupClass.coe_sub]
    first
    | rw [HahnSeries.coeff_sub]
    | rw [HahnSeries.sub_coeff]
    | simp only [HahnSeries.coeff_sub', Pi.sub_apply]
    rw [coe_sum_single_smul_coeff, coe_sum_single_smul_coeff, ht0, map_one]
    rfl
  have hLHS : ∀ m : ℤ, 0 ≤ padicValRat p ((((∑ i, cv i • frickeInvolutionFull (1 * p) (D.tRat i) :
      ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m) := by
    intro m
    rw [hsum]
    by_cases hm : m = 0
    · subst hm
      rw [HahnSeries.coeff_one]
      simp
    · rw [HahnSeries.coeff_one, if_neg hm, mul_zero, sub_zero]
      by_cases hbm : b m = 0
      · rw [hbm, mul_zero, padicValRat.zero]
      · rw [padicValRat.mul (inv_ne_zero hp0) hbm, padicValRat.inv, padicValRat.self hp.one_lt]
        have := hbpos m hm hbm
        omega
  have hRHS := (horthZero cv).mp hLHS l
  rw [hcv, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hll₀, sub_zero, padicValRat.inv,
    padicValRat.self hp.one_lt, h0n] at hRHS
  simp at hRHS

end OrthOne

section OrthZ1

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.inf_h0_of_one_le_hasseExp (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hge1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp D l) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → ∀ m : ℤ, 0 ≤ padicValRat p ((p : ℚ)⁻¹ *
      ((frickeInvolutionFull (1 * p) (D.tRat l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m) := by
  intro l hl m
  have hp : (p : ℕ).Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  have hcontent := isContent_hasseContent D l (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l)
  have hcast := hasseExp_cast D l (FamData.hasseContent_nonneg_of_orth p D hbasis horthZero l)
  by_cases hbm : (zeroSeries D l).coeff m = 0
  · show 0 ≤ padicValRat p ((p : ℚ)⁻¹ * (zeroSeries D l).coeff m)
    rw [hbm, mul_zero, padicValRat.zero]
  · show 0 ≤ padicValRat p ((p : ℚ)⁻¹ * (zeroSeries D l).coeff m)
    rw [padicValRat.mul (inv_ne_zero hp0) hbm, padicValRat.inv, padicValRat.self hp.one_lt]
    have h1 := hcontent.1 m hbm
    have h2 := hge1 l hl
    have h3 : (1 : ℤ) ≤ hasseContent D l := by rw [← hcast]; exact_mod_cast h2
    omega

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.hasseExp_le_one_of_orth_of_node (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728)
    (hnode1 : ∃ hint : ∀ l, D.t l ∈ (infChart Γ).integers, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      ∃ e : Fin (mAnnuli p), (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D.t l, hint l⟩) = 1) :
    ∀ l : Fin r, hasseExp D l ≤ 1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  intro l
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_eq_zero_of_t_eq_one D l (hzero l hl)]; omega
  have hl1 : 1 ≤ (l : ℕ) := by omega
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint1, hnode⟩ := hnode1
  obtain ⟨e, he1⟩ := hnode l hl1
  obtain ⟨hC, hres⟩ := FamData.exists_infChart_residue_t_ne_zero_of_orthInf p D horthInf A hA Γ l
  obtain ⟨hint0, hres0⟩ := FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ
  set n := hasseExp D l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (D.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := FamData.t_pole p D hbasis l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (D.t l) hC hres ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA (hint0 l) (hres0 l) hpole
  rw [he1, zpow_one] at hb
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  rw [hmodval, map_pow, map_pow, jWidth_of_ne (hw1 e).1 (hw1 e).2, pow_one] at hb
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0

  have : μ (p : AlgebraicClosure ℚ) ^ 1 ≤ μ (p : AlgebraicClosure ℚ) ^ n := by rwa [pow_one]
  exact (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp this

end OrthZ1

section OrthWrap

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (D : FamData p r)

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
include hp5 in

theorem FamData.hasseExp_le_one_of_orth
    (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∀ l : Fin r, hasseExp D l ≤ 1 := by
  have hr : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 D.t hbasis
  have hg0 : ∀ l : Fin r, (l : ℕ) = 0 → D.tRat l = 1 := fun l hl =>
    FamData.tRat_eq_one_of_t_eq_one p D l (hzero l hl)
  have hW : ∀ l : Fin r, (⟨coeffEmb (AlgebraicClosure ℚ) ↑(D.tRat l),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (D.tRat l).2⟩ : ↥(modularFunctionFieldBar (1 * p)))
        ∈ riemannRochSpace (embDivisor (1 * p)) := by
    intro l; rw [← D.t_eq l]; exact FamData.t_mem_riemannRochSpace p D hbasis l
  have hge1 := FamData.one_le_hasseExp_of_orth p D hzero hbasis horthInf horthZero A hA Γ
  have h0 := FamData.inf_h0_of_one_le_hasseExp p D hbasis horthZero hge1
  obtain ⟨hintM, -, P, hP, hli, -⟩ :=
    infChart_residue_eq_ssPolyBar_mul_of_orthogonal p hp5 hr D.tRat hg0 hW horthInf h0 A hA Γ
  have hint : ∀ l, D.t l ∈ (infChart Γ).integers := by
    intro l; rw [D.t_eq l]; exact hintM l
  have hnode : ∀ l : Fin r, 1 ≤ (l : ℕ) →
      ∃ e : Fin (mAnnuli p), (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D.t l, hint l⟩) = 1 := by
    intro l hl
    have hPl : P l ≠ 0 := hli.ne_zero ⟨l, hl⟩
    have hsub : (⟨D.t l, hint l⟩ : (infChart Γ).integers)
        = ⟨(⟨coeffEmb (AlgebraicClosure ℚ) ↑(D.tRat l),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (D.tRat l).2⟩ : ↥(modularFunctionFieldBar (1 * p))), hintM l⟩ :=
      Subtype.ext (D.t_eq l)
    rw [hsub]
    exact exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul Γ _ (hintM l) (P l) hPl (hP l hl).1 (hP l hl).2
  exact FamData.hasseExp_le_one_of_orth_of_node p D hzero hbasis horthInf horthZero A hA Γ Δ hw1 ⟨hint, hnode⟩

end OrthWrap

namespace ZXLocalT
open AlgebraicCurve IsLocalRing

theorem anntight_local
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (h : F) (hC : h ∈ C.integers) (hres : C.residue ⟨h, hC⟩ ≠ 0)
    (c' : L) (hc'0 : c' ≠ 0) (hc'A : c' ∈ A)
    (hC' : (algebraMap L F c')⁻¹ * h ∈ C'.integers) (hres' : C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩ ≠ 0)
    (hpole : ∀ Q ∈ An.dom, 0 ≤ Q.ord h)
    (hca : μ c' = μ (An.modulus : L) ^ x.ord (C.residue ⟨h, hC⟩)) :
    (∀ Q ∈ An.dom, Q.ord h = 0) ∧
      x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) = - x.ord (C.residue ⟨h, hC⟩) := by
  obtain ⟨D, hD0, hDsupp, hDord, hsum, hlog⟩ :=
    Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA An An' hdom hmod hmod0 htwo C x hatt
      C' x' hatt' hwide h hC hres c' hc'0 hc'A hC' hres' hpole
  set a := x.ord (C.residue ⟨h, hC⟩) with ha_def
  set a' := x'.ord (C'.residue ⟨(algebraMap L F c')⁻¹ * h, hC'⟩) with ha'_def
  have hμmod : 0 < μ (An.modulus : L) := μ.pos hmod0

  have hz : ∀ Q ∈ An.dom, Real.log (μ (An.modulus : L)) < Real.log (μ (Q.evalAt An.param)) := by
    intro Q hQ
    obtain ⟨-, -, -, hz0, m, hm, hmz⟩ := An.mem_dom Q hQ
    have hzpos : 0 < μ (Q.evalAt An.param) := μ.pos hz0
    apply Real.log_lt_log hμmod
    rw [hmz, map_mul]
    have hm1 : μ (m : L) < 1 := by
      have hmn : (m : L) ∈ A.nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr hm
      by_contra hge
      push_neg at hge
      have hmu : μ (m : L) = 1 := le_antisymm ((hμA _).mp m.2) hge

      have hm0 : (m : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at hmu; exact zero_ne_one hmu
      have hinv : (m : L)⁻¹ ∈ A := (hμA _).mpr (by rw [map_inv₀, hmu, inv_one])
      have hunit : IsUnit m := by
        refine ⟨⟨m, ⟨(m : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0), Subtype.ext (inv_mul_cancel₀ hm0)⟩, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mp hm hunit
    calc μ (Q.evalAt An.param) * μ (m : L) < μ (Q.evalAt An.param) * 1 :=
          mul_lt_mul_of_pos_left hm1 hzpos
      _ = μ (Q.evalAt An.param) := mul_one _

  have hlc : Real.log (μ c') = (a : ℝ) * Real.log (μ (An.modulus : L)) := by
    rw [hca, Real.log_zpow]

  have hDzero : ∀ Q, D Q = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨Q₀, hQ₀⟩ := hne
    have hQ₀pos : 0 < D Q₀ := lt_of_le_of_ne (hD0 Q₀) (Ne.symm hQ₀)
    have hQ₀supp : Q₀ ∈ D.support := Finsupp.mem_support_iff.mpr hQ₀

    have hlt : ((a + a' : ℤ) : ℝ) * Real.log (μ (An.modulus : L))
        < D.sum (fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt An.param))) := by
      rw [← hsum, Finsupp.sum, Finsupp.sum, Int.cast_sum, Finset.sum_mul]
      apply Finset.sum_lt_sum
      · intro Q hQ
        have hQdom : Q ∈ An.dom := hDsupp Q (Finsupp.mem_support_iff.mp hQ)
        exact mul_le_mul_of_nonneg_left (hz Q hQdom).le (by exact_mod_cast hD0 Q)
      · exact ⟨Q₀, hQ₀supp, mul_lt_mul_of_pos_left (hz Q₀ (hDsupp Q₀ hQ₀)) (by exact_mod_cast hQ₀pos)⟩
    rw [hlog, hlc] at hlt
    push_cast at hlt
    linarith
  have hsum0 : a + a' = 0 := by
    rw [← hsum, Finsupp.sum]
    exact Finset.sum_eq_zero fun Q _ => hDzero Q
  refine ⟨fun Q hQ => ?_, by omega⟩
  rw [← hDord Q hQ, hDzero Q]

end ZXLocalT

section CTight

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

theorem jBar_sub_algebraMap_ne_zero' (c : ResidueField ↥A) :
    jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (ResidueField ↥A) c c
  rw [if_pos rfl] at this
  have h' : (charLGeomPlaceOfPoint (ResidueField ↥A) c).ord
      (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) = 0 := by rw [h, Place.ord_zero]
  rw [h'] at this
  exact zero_ne_one this

theorem ord_charLGeomPlaceOfPoint_prod_jBar_sub' (T : Finset (ResidueField ↥A)) (a : ResidueField ↥A) :
    (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord
      (∏ b ∈ T, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ b)) = if a ∈ T then 1 else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | @insert b T hb ih =>
    rw [Finset.prod_insert hb, Place.ord_mul _ (jBar_sub_algebraMap_ne_zero' A b)
      (Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A x), ih,
      ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap]
    by_cases hab : b = a
    · subst hab
      simp [Finset.mem_insert, hb]
    · have hab' : ¬ a = b := fun h => hab h.symm
      simp [Finset.mem_insert, hab, hab']

theorem ssPolyBar_eq_prod' : ssPolyBar Γ = ∏ e : Fin (mAnnuli p),
    (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) := rfl

theorem ord_nodeTgt_prod' (T : Finset (Fin (mAnnuli p))) (e : Fin (mAnnuli p)) :
    (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord
      (∏ e' ∈ T, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e'))) = if e ∈ T then 1 else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | @insert b T hb ih =>
    rw [Finset.prod_insert hb, Place.ord_mul _ (jBar_sub_algebraMap_ne_zero' A _)
      (Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _), ih,
      ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap]
    by_cases hab : b = e
    · subst hab
      simp [Finset.mem_insert, hb]
    · have hab' : ¬ e = b := fun h => hab h.symm
      have hval : ¬ ssValue Γ b = ssValue Γ e := fun h => hab (ssValue_injective Γ h)
      simp [Finset.mem_insert, hab', hval]

theorem ord_nodeTgt_ssPolyBar' (e : Fin (mAnnuli p)) :
    (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ) = 1 := by
  rw [ssPolyBar_eq_prod', ord_nodeTgt_prod', if_pos (Finset.mem_univ e)]

set_option maxHeartbeats 6400000 in
include hA Δ in

theorem ord_nodeSrc_eq_neg_of_hasseTight'
    (e : Fin (mAnnuli p)) (h : modularFunctionFieldBar (1 * p)) (hC : h ∈ (infChart Γ).integers)
    (hres : (infChart Γ).residue ⟨h, hC⟩ ≠ 0)
    (hfpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord h < 0 → W = cuspInftyBar (1 * p))
    (n : ℕ) (hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * h
      ∈ (zeroChart Γ).integers)
    (hres' : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0)
    (hna : (n : ℤ) = (jWidth (ssValue Γ e) : ℤ) * (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩)) :
    (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨_, hC'⟩) = - (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h0 : h ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : modularFunctionFieldBar (1 * p)), hC⟩ : (infChart Γ).integers) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord h := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := hfpole Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hca : μ ((p : AlgebraicClosure ℚ) ^ n)
      = μ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ^ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩) := by
    rw [hmodval, map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← hna]
  exact (ZXLocalT.anntight_local μ hμA (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt
    (zeroChart Γ) (nodeSrc Γ e) hatt' hwide h hC hres ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    hC' hres' hpole hca).2

set_option maxHeartbeats 6400000 in
include hA Δ in

theorem ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul'
    (e : Fin (mAnnuli p)) (h : modularFunctionFieldBar (1 * p)) (hC : h ∈ (infChart Γ).integers)
    (hres : (infChart Γ).residue ⟨h, hC⟩ ≠ 0)
    (hfpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord h < 0 → W = cuspInftyBar (1 * p))
    (n : ℕ) (hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * h
      ∈ (zeroChart Γ).integers)
    (hres' : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0)
    (hna : (n : ℤ) = (jWidth (ssValue Γ e) : ℤ) * (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩)) :
    (∀ Q ∈ (Δ.annIn e).dom, Q.ord h = 0) ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨_, hC'⟩) = - (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord h := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := hfpole Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  have hca : μ ((p : AlgebraicClosure ℚ) ^ n)
      = μ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ^ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩) := by
    rw [hmodval, map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← hna]
  have key := ZXLocalT.anntight_local μ hμA (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt
    (zeroChart Γ) (nodeSrc Γ e) hatt' hwide h hC hres ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    hC' hres' hpole hca
  exact ⟨fun Q hQ => key.1 Q (hdom ▸ hQ), key.2⟩

theorem exists_mem_span_ord_nodeSrc_eq_zero'
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers) (e : Fin (mAnnuli p)) (l₀ : Fin r)
    (hl₀ : (l₀ : ℕ) = 0) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f = 0 := by
  have hg1 : goodFamilyZero Φ.toFamData l₀ = 1 := by
    have h1 : Φ.t l₀ = 1 := Φ.t_zero l₀ hl₀
    show (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₀))⁻¹ * Φ.t l₀ = 1
    rw [hasseExp_eq_zero_of_t_eq_one Φ.toFamData l₀ h1, pow_zero, map_one, inv_one, h1, mul_one]
  refine ⟨(zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₀, hint l₀⟩, Submodule.subset_span ⟨l₀, rfl⟩, ?_⟩
  have hsub : (⟨goodFamilyZero Φ.toFamData l₀, hint l₀⟩ : (zeroChart Γ).integers) = 1 := Subtype.ext hg1
  rw [hsub, map_one, Place.ord_one]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 6400000 in
include hA Δ in

theorem exists_mem_span_ord_nodeSrc_eq_neg_of_combination'
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers)
    (P : Fin r → Polynomial (ResidueField ↥A))
    (hP : ∀ l : Fin r, 1 ≤ (l : ℕ) →
      (infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l))
    (n : ℕ) (hn1 : 1 ≤ n) (c : Fin r → ResidueField ↥A)
    (hc : ∀ l, c l ≠ 0 → hasseExp Φ.toFamData l = n) (hc0 : ∃ l, c l ≠ 0)
    (R : Polynomial (ResidueField ↥A)) (hR : ∑ l, c l • P l = R) (e : Fin (mAnnuli p))
    (hna : (n : ℤ) = (jWidth (ssValue Γ e) : ℤ) *
      (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) R)) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f
        = -(charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) R) := by
  classical
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hc1 : ∀ l, c l ≠ 0 → 1 ≤ (l : ℕ) := by
    intro l hl
    by_contra hlt
    push_neg at hlt
    have h0 : (l : ℕ) = 0 := by omega
    have := hc l hl
    rw [hasseExp_zero p Φ l h0] at this
    omega

  have hlift : ∀ l, ∃ a : ↥A, IsLocalRing.residue ↥A a = c l ∧ (c l = 0 → a = 0) := by
    intro l
    by_cases h0 : c l = 0
    · exact ⟨0, by rw [h0, map_zero], fun _ => rfl⟩
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (c l)
      exact ⟨a, ha, fun h => (h0 h).elim⟩
  choose ct hct hct0 using hlift

  set aI : Fin r → (infChart Γ).integers := fun l =>
    ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (ct l : AlgebraicClosure ℚ), ((infChart Γ).algebraMap_mem_iff _).mpr (ct l).2⟩ with haI
  set aZ : Fin r → (zeroChart Γ).integers := fun l =>
    ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (ct l : AlgebraicClosure ℚ), ((zeroChart Γ).algebraMap_mem_iff _).mpr (ct l).2⟩ with haZ
  set H : (infChart Γ).integers := ∑ l, aI l * ⟨goodFamily Φ l, hintI l⟩ with hH
  set K : (zeroChart Γ).integers := ∑ l, aZ l * ⟨goodFamilyZero Φ.toFamData l, hint l⟩ with hK
  have hHval : (H : modularFunctionFieldBar (1 * p)) = ∑ l, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (ct l : AlgebraicClosure ℚ) * Φ.t l := by
    rw [hH]; push_cast; rfl
  have hKval : (K : modularFunctionFieldBar (1 * p)) = ∑ l, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (ct l : AlgebraicClosure ℚ) * goodFamilyZero Φ.toFamData l := by
    rw [hK]; push_cast; rfl

  have hKH : (K : modularFunctionFieldBar (1 * p)) = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * (H : modularFunctionFieldBar (1 * p)) := by
    rw [hKval, hHval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h0 : c l = 0
    · rw [hct0 l h0]; simp
    · show algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (ct l : AlgebraicClosure ℚ) *
          ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * Φ.t l) = _
      rw [hc l h0]; ring

  have hresI : (infChart Γ).residue H = ∑ l, algebraMap (ResidueField ↥A) _ (c l) * (infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩ := by
    rw [hH, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, haI]
    simp only []
    rw [(infChart Γ).residue_algebraMap (ct l), hct l]
  have hresZ : (zeroChart Γ).residue K = ∑ l, algebraMap (ResidueField ↥A) _ (c l) * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ := by
    rw [hK, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, haZ]
    simp only []
    rw [(zeroChart Γ).residue_algebraMap (ct l), hct l]

  have hresI' : (infChart Γ).residue H = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) R := by
    rw [hresI, ← hR, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h0 : c l = 0
    · rw [h0]; simp
    · rw [hP l (hc1 l h0), map_smul, Algebra.smul_def]; ring

  have hresI0 : (infChart Γ).residue H ≠ 0 := by
    intro h0
    rw [hresI'] at h0
    rw [h0, Place.ord_zero, mul_zero] at hna
    omega
  have hresZ0 : (zeroChart Γ).residue K ≠ 0 := by
    intro h0
    rw [hresZ] at h0
    have hall := Fintype.linearIndependent_iff.mp hLI c (by simpa [Algebra.smul_def] using h0)
    obtain ⟨l, hl⟩ := hc0
    exact hl (hall l)

  have hHpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (H : modularFunctionFieldBar (1 * p)) < 0 → W = cuspInftyBar (1 * p) := by
    intro W hW
    by_contra hne
    have hmem : (H : modularFunctionFieldBar (1 * p)) ∈ W.toValuationSubring := by
      rw [hHval]
      refine sum_mem fun l _ => mul_mem (W.algebraMap_mem' _) ?_
      have ht0 := t_ne_zero p Φ l
      refine Place.mem_of_ord_nonneg _ ht0 ?_
      by_contra hlt
      push_neg at hlt
      exact hne (t_pole p Φ l W hlt)
    have := Place.ord_nonneg_of_mem W hmem
    omega

  have horda : (nodeTgt Γ e).ord ((infChart Γ).residue H)
      = (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) R) := by
    rw [hresI']; rfl

  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * (H : modularFunctionFieldBar (1 * p)) ∈ (zeroChart Γ).integers := by
    rw [← hKH]; exact K.2
  have hKsub : (⟨(algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * (H : modularFunctionFieldBar (1 * p)), hC'⟩ : (zeroChart Γ).integers) = K :=
    Subtype.ext hKH.symm
  have hres'0 : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0 := by rw [hKsub]; exact hresZ0
  have hna' : (n : ℤ) = (jWidth (ssValue Γ e) : ℤ) * (nodeTgt Γ e).ord ((infChart Γ).residue ⟨(H : modularFunctionFieldBar (1 * p)), H.2⟩) := by
    rw [Subtype.coe_eta, horda]; exact hna
  have key := ord_nodeSrc_eq_neg_of_hasseTight' p A hA Γ Δ e (H : modularFunctionFieldBar (1 * p)) H.2 (by rw [Subtype.coe_eta]; exact hresI0) hHpole n hC'
    hres'0 hna'
  rw [hKsub, Subtype.coe_eta, horda, hresZ] at key
  refine ⟨_, ?_, key⟩
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

end CTight

section CTightAsm

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

theorem aeval_jBar_prod_X_sub_C' (T : Finset (Fin (mAnnuli p))) :
    Polynomial.aeval (jBar (ResidueField ↥A)) (∏ e ∈ T, (Polynomial.X - Polynomial.C (ssValue Γ e)))
      = ∏ e ∈ T, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) := by
  rw [map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

include hA Δ in

theorem exists_mem_span_ord_nodeSrc_eq_neg_one' (hp5 : 5 ≤ p)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (hw : jWidth (ssValue Γ e) = 1) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f = -1 := by
  classical
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : ExpChar (ResidueField ↥A) p := ExpChar.prime Fact.out
  set g : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e ^ p) with hg
  have hg0 : g ≠ 0 := jBar_sub_algebraMap_ne_zero' A _
  set f : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := g⁻¹ with hf

  have hfin : ∀ c : ResidueField ↥A, (charLGeomPlaceOfPoint (ResidueField ↥A) c).ord f = if ssValue Γ e ^ p = c then -1 else 0 := by
    intro c
    rw [hf, Place.ord_inv, hg, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap]
    split_ifs <;> simp
  have hinf : 0 ≤ (charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A))).ord f := by
    set v := charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A))
    have hj : v.ord (jBar (ResidueField ↥A)) = -1 := ord_charLGeomPlaceEquiv_placeInfty_jqModC (ResidueField ↥A)
    have hj0 : jBar (ResidueField ↥A) ≠ 0 := fun h => by rw [h, Place.ord_zero] at hj; omega

    have hgle : v.ord g < 0 := by
      by_contra hge
      push_neg at hge
      by_cases hc0 : algebraMap (ResidueField ↥A) (↥(modularFunctionFieldC (ResidueField ↥A) 1)) (ssValue Γ e ^ p) = 0
      · rw [hg, hc0, sub_zero] at hge; omega
      · have := Place.min_ord_le_ord_add v hg0 hc0 (by rw [hg, sub_add_cancel]; exact hj0)
        rw [hg, sub_add_cancel, hj, Place.ord_algebraMap] at this
        have h2 : min (v.ord (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e ^ p))) 0 = 0 := min_eq_right hge
        rw [← hg] at h2; rw [← hg, h2] at this; omega
    rw [hf, Place.ord_inv]; omega

  have hreg : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord f := by
    intro v hv
    rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (ResidueField ↥A) v with ⟨c, rfl⟩ | rfl
    · rw [hfin]
      split_ifs with hc
      · exact absurd ((mem_zeroChart_nodes_iff Γ _).mpr ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, by rw [hc]⟩) hv
      · exact le_rfl
    · exact hinf

  have hnode : ∀ e' : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e') : ℕ) : ℤ) ≤ (nodeSrc Γ e').ord f := by
    intro e'
    show _ ≤ (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e' ^ p)).ord f
    rw [hfin]
    split_ifs with hc
    · have hee : e = e' := ssValue_injective Γ (frobenius_inj (ResidueField ↥A) p hc)
      subst hee; rw [hw]; norm_num
    · have : 0 ≤ (1 / jWidth (ssValue Γ e') : ℕ) := Nat.zero_le _
      omega
  refine ⟨f, mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge p hp5 A hA Γ Δ Φ hint hLI f hreg hnode, ?_⟩
  show (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e ^ p)).ord f = -1
  rw [hfin, if_pos rfl]

include hA Δ in

theorem exists_mem_span_zeroChart_residue_ord_nodeSrc_eq_neg_hasseExp_div_jWidth_of_thirteen_le' (hp13 : 13 ≤ p)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (l : Fin r) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ) := by
  classical
  have hp5 : 5 ≤ p := by omega
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) l.2
  set l₀ : Fin r := ⟨0, hr⟩ with hl₀
  have hn2 := hasseExp_le_two_of_thirteen_le p hp13 A hA Γ Δ Φ l
  have hw123 := jWidth_eq_one_or (ssValue Γ e)

  by_cases hv0 : hasseExp Φ.toFamData l / jWidth (ssValue Γ e) = 0
  · rw [hv0]; simpa using exists_mem_span_ord_nodeSrc_eq_zero' p A Γ Φ hint e l₀ rfl

  have hwn : jWidth (ssValue Γ e) ≤ hasseExp Φ.toFamData l := by
    by_contra h; push_neg at h; exact hv0 (Nat.div_eq_of_lt h)
  rcases hw123 with h1 | h2 | h3
  ·
    rw [h1, Nat.div_one]
    rw [h1] at hwn
    have hn12 : hasseExp Φ.toFamData l = 1 ∨ hasseExp Φ.toFamData l = 2 := by omega
    rcases hn12 with hn1' | hn2'
    ·
      rw [hn1']
      simpa using exists_mem_span_ord_nodeSrc_eq_neg_one' p A hA Γ Δ Φ hp5 hint hLI e (h1)
    ·
      rw [hn2']

      have hwide : ∃ e' : Fin (mAnnuli p), jWidth (ssValue Γ e') ≠ 1 := by
        by_contra hall
        push_neg at hall
        have hw1 : ∀ e', ssValue Γ e' ≠ 0 ∧ ssValue Γ e' ≠ 1728 := by
          intro e'
          have h := hall e'
          refine ⟨fun h0 => ?_, fun h1728 => ?_⟩
          · rw [jWidth_of_eq_zero h0] at h; omega
          · by_cases h0 : ssValue Γ e' = 0
            · rw [jWidth_of_eq_zero h0] at h; omega
            · rw [jWidth_of_eq_1728 h1728 h0] at h; omega
        have := hasseExp_le_one_of_forall_widthOne p A hA Γ Δ Φ hw1 l
        omega
      obtain ⟨hintI, -, P, hP, hli, -⟩ := infChart_residue_goodFamily p A hA Γ Φ
      obtain ⟨c, hc2, hcR⟩ := exists_combination_hasseExp_two_eq_prod_widthOne p hp13 A hA Γ Δ Φ hint hLI hwide hintI P hP hli
      set S := Finset.univ.filter (fun e => jWidth (ssValue Γ e) = 1) with hS
      have heS : e ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ e, h1⟩
      have hord : (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord
          (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (∏ e' ∈ S, (Polynomial.X - Polynomial.C (ssValue Γ e')))) = 2 := by
        rw [aeval_jBar_prod_X_sub_C', Place.ord_mul _ ?_ ?_, ord_nodeTgt_ssPolyBar', ord_nodeTgt_prod', if_pos heS]
        · rfl
        · rw [ssPolyBar_eq_prod']; exact Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _
        · exact Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _
      have hc0 : ∃ l', c l' ≠ 0 := by
        by_contra hall; push_neg at hall
        have : ∑ l', c l' • P l' = 0 := Finset.sum_eq_zero fun l' _ => by rw [hall l', zero_smul]
        rw [this] at hcR
        exact (Monic.ne_zero (monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _)) hcR.symm
      obtain ⟨f, hf, hfo⟩ := exists_mem_span_ord_nodeSrc_eq_neg_of_combination' p A hA Γ Δ Φ hint hLI hintI P
        (fun l' hl' => (hP l' hl').2) 2 (by norm_num) c hc2 hc0 _ hcR e (by rw [hord, h1]; norm_num)
      exact ⟨f, hf, by rw [hfo, hord]; rfl⟩
  ·
    rw [h2] at hwn ⊢
    have hn' : hasseExp Φ.toFamData l = 2 := by omega
    rw [hn']
    show ∃ f ∈ _, (nodeSrc Γ e).ord f = -((2 / 2 : ℕ) : ℤ)
    have hwide : ∃ e' : Fin (mAnnuli p), jWidth (ssValue Γ e') ≠ 1 := ⟨e, by rw [h2]; omega⟩
    obtain ⟨hintI, -, P, hP, hli, -⟩ := infChart_residue_goodFamily p A hA Γ Φ
    obtain ⟨c, hc2, hcR⟩ := exists_combination_hasseExp_two_eq_prod_widthOne p hp13 A hA Γ Δ Φ hint hLI hwide hintI P hP hli
    set S := Finset.univ.filter (fun e => jWidth (ssValue Γ e) = 1) with hS
    have heS : e ∉ S := by rw [hS, Finset.mem_filter]; rintro ⟨-, h⟩; rw [h2] at h; omega
    have hord : (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord
        (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (∏ e' ∈ S, (Polynomial.X - Polynomial.C (ssValue Γ e')))) = 1 := by
      rw [aeval_jBar_prod_X_sub_C', Place.ord_mul _ ?_ ?_, ord_nodeTgt_ssPolyBar', ord_nodeTgt_prod', if_neg heS]
      · rfl
      · rw [ssPolyBar_eq_prod']; exact Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _
      · exact Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _
    have hc0 : ∃ l', c l' ≠ 0 := by
      by_contra hall; push_neg at hall
      have : ∑ l', c l' • P l' = 0 := Finset.sum_eq_zero fun l' _ => by rw [hall l', zero_smul]
      rw [this] at hcR
      exact (Monic.ne_zero (monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _)) hcR.symm
    obtain ⟨f, hf, hfo⟩ := exists_mem_span_ord_nodeSrc_eq_neg_of_combination' p A hA Γ Δ Φ hint hLI hintI P
      (fun l' hl' => (hP l' hl').2) 2 (by norm_num) c hc2 hc0 _ hcR e (by rw [hord, h2]; norm_num)
    exact ⟨f, hf, by rw [hfo, hord]; rfl⟩
  ·
    exfalso; apply hv0; rw [h3]; exact Nat.div_eq_of_lt (by omega)

end CTightAsm

section CTightSmall

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA Δ in

theorem hasseExp_le_jWidth_mul_ord_nodeTgt'
    (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (e : Fin (mAnnuli p)) (l : Fin r)
    (ha : 0 ≤ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩)) :
    (hasseExp Φ.toFamData l : ℤ) ≤ (jWidth (ssValue Γ e) : ℤ) * (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩) := by
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hb, -⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hintI hres_ne hint0 hres0 e l
  set a := (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩) with ha_def
  set n := hasseExp Φ.toFamData l
  set w := jWidth (ssValue Γ e)
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  obtain ⟨a', ha'⟩ := Int.eq_ofNat_of_zero_le ha
  rw [ha', zpow_natCast, ← pow_mul] at hb
  have := (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp hb
  rw [ha']; exact_mod_cast this

include hA Δ in

theorem exists_mem_span_ord_nodeSrc_eq_of_mAnnuli_eq_one' (hm : mAnnuli p = 1)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (l : Fin r) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ) := by
  classical
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) l.2
  set l₀ : Fin r := ⟨0, hr⟩ with hl₀
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl, Nat.zero_div]
    simpa using exists_mem_span_ord_nodeSrc_eq_zero' p A Γ Φ hint e l₀ rfl
  have hl1 : 1 ≤ (l : ℕ) := by omega
  obtain ⟨hintI, -, P, hP, hli, -⟩ := infChart_residue_goodFamily p A hA Γ Φ

  have hPl0 : P l ≠ 0 := hli.ne_zero ⟨l, hl1⟩
  have hdeg : (P l).natDegree = 0 := by have := (hP l hl1).1; rw [hm] at this; omega
  obtain ⟨c0, hc0⟩ : ∃ c0, P l = Polynomial.C c0 := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
  have hc0ne : c0 ≠ 0 := by rintro rfl; rw [map_zero] at hc0; exact hPl0 hc0

  have hord : (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).ord
      (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l)) = 1 := by
    rw [hc0, Polynomial.aeval_C, Place.ord_mul _ ?_ ((_root_.map_ne_zero _).mpr hc0ne), ord_nodeTgt_ssPolyBar',
      Place.ord_algebraMap, add_zero]
    rw [ssPolyBar_eq_prod']; exact Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _

  have hres_eq := (hP l hl1).2
  have h2 : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hintI l⟩) = 1 := by
    show (charLGeomPlaceOfPoint _ _).ord _ = 1; rw [hres_eq, hord]
  have hnw : (hasseExp Φ.toFamData l : ℤ) ≤ (jWidth (ssValue Γ e) : ℤ) * 1 := by
    have h := hasseExp_le_jWidth_mul_ord_nodeTgt' p A hA Γ Δ Φ hintI e l (zero_le_one.trans h2.ge)
    rwa [h2] at h
  have hwpos : 0 < jWidth (ssValue Γ e) := jWidth_pos _
  by_cases hnw' : hasseExp Φ.toFamData l < jWidth (ssValue Γ e)
  · rw [Nat.div_eq_of_lt hnw']
    simpa using exists_mem_span_ord_nodeSrc_eq_zero' p A Γ Φ hint e l₀ rfl
  have hneq : hasseExp Φ.toFamData l = jWidth (ssValue Γ e) := by
    push_neg at hnw'
    have : (hasseExp Φ.toFamData l : ℤ) ≤ jWidth (ssValue Γ e) := by simpa using hnw
    omega
  rw [hneq, Nat.div_self hwpos]

  obtain ⟨f, hf, hfo⟩ := exists_mem_span_ord_nodeSrc_eq_neg_of_combination' p A hA Γ Δ Φ hint hLI hintI P
    (fun l' hl' => (hP l' hl').2) (hasseExp Φ.toFamData l) (by have := one_le_hasseExp p A hA Γ Φ l hl1; omega) (Pi.single l 1)
    (fun l' hl' => by
      by_cases h : l' = l
      · subst h; rfl
      · rw [Pi.single_eq_of_ne h] at hl'; exact (hl' rfl).elim)
    ⟨l, by rw [Pi.single_eq_same]; exact one_ne_zero⟩ (P l)
    (by rw [Finset.sum_eq_single l (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
      (fun h => (h (Finset.mem_univ l)).elim), Pi.single_eq_same, one_smul]) e
    (by rw [hord, mul_one]; exact_mod_cast hneq)
  exact ⟨f, hf, by rw [hfo, hord]; norm_num⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 6400000 in
include hA Δ in

theorem exists_mem_span_ord_nodeSrc_eq_of_mAnnuli_eq_two_of_forall_wide' (hm : mAnnuli p = 2) (hp5 : 5 ≤ p)
    (hwide : ∀ e, jWidth (ssValue Γ e) ≠ 1)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (l : Fin r) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ) := by
  classical
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hr3 : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 Φ.t Φ.t_basis
  have hr : 0 < r := by omega
  set l₀ : Fin r := ⟨0, hr⟩ with hl₀
  have C0 : ∀ e', ∃ f ∈ Submodule.span (ResidueField ↥A)
      (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩), (nodeSrc Γ e').ord f = 0 :=
    fun e' => exists_mem_span_ord_nodeSrc_eq_zero' p A Γ Φ hint e' l₀ rfl
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl, Nat.zero_div]; simpa using C0 e
  have hl1 : 1 ≤ (l : ℕ) := by omega
  obtain ⟨hintI, -, P, hP, hli, -⟩ := infChart_residue_goodFamily p A hA Γ Φ
  have hq1 : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)

  have hw2 : ∀ e', 2 ≤ jWidth (ssValue Γ e') := by
    intro e'; rcases jWidth_eq_one_or (ssValue Γ e') with h | h | h <;> [exact absurd h (hwide e'); omega; omega]
  obtain ⟨hintF, hF1⟩ := neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero p A hA Γ Δ Φ
  obtain ⟨hintZ, hZ3⟩ := zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p A hA Γ Φ
  have hne1 : ∀ l' : Fin r, 1 ≤ (l' : ℕ) → hasseExp Φ.toFamData l' ≠ 1 := by
    intro l' hl'1 h1

    have hall : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
        0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩) := by
      intro v
      by_cases hv : v ∈ (zeroChart Γ).nodes
      · obtain ⟨a, ha, hav⟩ := (mem_zeroChart_nodes_iff Γ v).mp hv
        obtain ⟨e', he'⟩ := exists_ssValue_eq Γ a ha
        have : v = nodeSrc Γ e' := by rw [← hav, ← he']; rfl
        rw [this]
        have h := hF1 e' l'
        rw [h1, Nat.div_eq_of_lt (by have := hw2 e'; omega)] at h
        simpa using h
      · exact hZ3 l' v hv
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_ord_nonneg (ResidueField ↥A) 1 hq1 _ hall
    have hl'0 : l' ≠ l₀ := by intro h; rw [h] at hl'1; simp [hl₀] at hl'1
    have h1res : (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₀, hint l₀⟩ = 1 := by
      have hg1 : goodFamilyZero Φ.toFamData l₀ = 1 := by
        have ht : Φ.t l₀ = 1 := Φ.t_zero l₀ rfl
        show (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l₀))⁻¹ * Φ.t l₀ = 1
        rw [hasseExp_eq_zero_of_t_eq_one Φ.toFamData l₀ ht, pow_zero, map_one, inv_one, ht, mul_one]
      have : (⟨goodFamilyZero Φ.toFamData l₀, hint l₀⟩ : (zeroChart Γ).integers) = 1 := Subtype.ext hg1
      rw [this, map_one]

    have hinj0 : Function.Injective (![l₀, l'] : Fin 2 → Fin r) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | (exfalso; simp at hij; first | exact hl'0 hij | exact hl'0 hij.symm)
    have hpair0 := hLI.comp _ hinj0
    have hpair0' : LinearIndependent (ResidueField ↥A)
        ![(zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₀, hint l₀⟩,
          (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩] := by
      convert hpair0 using 1
      ext i; fin_cases i <;> rfl
    have hdep := (LinearIndependent.pair_iff.mp hpair0') c (-1) (by
      rw [h1res, hc, Algebra.algebraMap_eq_smul_one, neg_one_smul, add_neg_cancel])
    exact one_ne_zero (neg_eq_zero.mp hdep.2)

  have hn3 := hasseExp_le_modulusExp p A hA Γ Δ Φ l
  rw [show modulusExp = 3 from rfl] at hn3
  have hn1 := one_le_hasseExp p A hA Γ Φ l hl1
  have hnl : hasseExp Φ.toFamData l = 2 ∨ hasseExp Φ.toFamData l = 3 := by
    have := hne1 l hl1; omega

  have hlt3 : (l : ℕ) < 3 := by have := l.2; omega
  obtain ⟨l', hl'1, hll'⟩ : ∃ l' : Fin r, 1 ≤ (l' : ℕ) ∧ l' ≠ l := by
    by_cases h1 : (l : ℕ) = 1
    · exact ⟨⟨2, by omega⟩, by simp, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩
    · exact ⟨⟨1, by omega⟩, by simp, fun h => by rw [Fin.ext_iff] at h; simp at h; omega⟩

  have hdegl : (P l).natDegree ≤ 1 := by have := (hP l hl1).1; rw [hm] at this; omega
  have hdegl' : (P l').natDegree ≤ 1 := by have := (hP l' hl'1).1; rw [hm] at this; omega
  have hpair : LinearIndependent (ResidueField ↥A) ![P l, P l'] := by
    have hinj : Function.Injective (![⟨l, hl1⟩, ⟨l', hl'1⟩] : Fin 2 → {x : Fin r // 1 ≤ (x : ℕ)}) := by
      intro i j hij
      have hij' := congrArg (fun x : {x : Fin r // 1 ≤ (x : ℕ)} => (x : Fin r)) hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | (exfalso; simp at hij'; first | exact hll' hij' | exact hll' hij'.symm)
    have := hli.comp _ hinj
    convert this using 1
    ext i; fin_cases i <;> rfl

  have hfactor : ∀ Q : Polynomial (ResidueField ↥A), Q.natDegree ≤ 1 → ∀ b, Q.eval b = 0 →
      Q = Polynomial.C Q.leadingCoeff * (Polynomial.X - Polynomial.C b) := by
    intro Q hQ b hb
    by_cases hQ0 : Q = 0
    · subst hQ0; simp
    obtain ⟨R, hR⟩ := (Polynomial.dvd_iff_isRoot.mpr hb : Polynomial.X - Polynomial.C b ∣ Q)
    have hR0 : R ≠ 0 := by rintro rfl; rw [mul_zero] at hR; exact hQ0 hR
    have hdR : R.natDegree = 0 := by
      have := congrArg Polynomial.natDegree hR
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero b) hR0, Polynomial.natDegree_X_sub_C] at this
      omega
    obtain ⟨q, rfl⟩ : ∃ q, R = Polynomial.C q := ⟨_, Polynomial.eq_C_of_natDegree_eq_zero hdR⟩
    have hlc : Q.leadingCoeff = q := by
      rw [hR, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_sub_C, one_mul, Polynomial.leadingCoeff_C]
    rw [hlc, hR, mul_comm]

  have hnotboth : ∀ b, ¬ ((P l).eval b = 0 ∧ (P l').eval b = 0) := by
    rintro b ⟨h1, h2⟩
    have e1 := hfactor (P l) hdegl b h1
    have e2 := hfactor (P l') hdegl' b h2
    have := (LinearIndependent.pair_iff.mp hpair) (P l').leadingCoeff (-(P l).leadingCoeff) (by
      rw [e1, e2]; simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_sub_C, mul_one]
      rw [smul_eq_C_mul, smul_eq_C_mul, map_neg]; ring)
    have hPl0 : P l ≠ 0 := hli.ne_zero ⟨l, hl1⟩
    exact hPl0 (Polynomial.leadingCoeff_eq_zero.mp (neg_eq_zero.mp this.2))

  have hordP : ∀ (m : Fin r), 1 ≤ (m : ℕ) → (P m).natDegree ≤ 1 → ∀ e', (P m).eval (ssValue Γ e') ≠ 0 →
      (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e')).ord
        (ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P m)) = 1 := by
    intro m hm1 hdm e' hev
    have hPm0 : P m ≠ 0 := hli.ne_zero ⟨m, hm1⟩
    obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
    have haeval0 : Polynomial.aeval (jBar (ResidueField ↥A)) (P m) ≠ 0 := by
      intro h0; apply hres_ne m
      rw [show (infChart Γ).residue ⟨goodFamily Φ m, hint2 m⟩ = (infChart Γ).residue ⟨goodFamily Φ m, hintI m⟩ from rfl,
        (hP m hm1).2, h0, mul_zero]

    have hval : (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e')).ord (Polynomial.aeval (jBar (ResidueField ↥A)) (P m)) = 0 := by
      set v := charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e') with hv_def

      obtain ⟨Q, hQ⟩ := (Polynomial.X_sub_C_dvd_sub_C_eval (p := P m) (a := ssValue Γ e'))
      have hdecomp : Polynomial.aeval (jBar (ResidueField ↥A)) (P m)
            - algebraMap (ResidueField ↥A) _ ((P m).eval (ssValue Γ e'))
          = (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e')) * Polynomial.aeval (jBar (ResidueField ↥A)) Q := by
        have := congrArg (Polynomial.aeval (jBar (ResidueField ↥A))) hQ
        rw [map_sub, Polynomial.aeval_C, map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at this
        exact this
      have hjmem : jBar (ResidueField ↥A) ∈ v.toValuationSubring := by
        have h1 : jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e') ∈ v.toValuationSubring :=
          Place.mem_of_ord_nonneg _ (jBar_sub_algebraMap_ne_zero' A _)
            (by rw [hv_def, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, if_pos rfl]; omega)
        have := add_mem h1 (v.algebraMap_mem' (ssValue Γ e'))
        rwa [sub_add_cancel] at this
      have haevmem : ∀ R : Polynomial (ResidueField ↥A), Polynomial.aeval (jBar (ResidueField ↥A)) R ∈ v.toValuationSubring := by
        intro R
        rw [Polynomial.aeval_eq_sum_range]
        refine sum_mem fun i _ => ?_
        rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) (pow_mem hjmem i)
      have hhas : v.HasValue (Polynomial.aeval (jBar (ResidueField ↥A)) (P m)) ((P m).eval (ssValue Γ e')) := by
        rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos]
        refine ⟨haevmem _, ?_⟩
        by_cases hQ0 : Polynomial.aeval (jBar (ResidueField ↥A)) Q = 0
        · left; rw [← sub_eq_zero, hdecomp, hQ0, mul_zero]
        · right
          rw [hdecomp, Place.ord_mul _ (jBar_sub_algebraMap_ne_zero' A _) hQ0, hv_def,
            ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, if_pos rfl]
          have := Place.ord_nonneg_of_mem v (haevmem Q)
          rw [hv_def] at this
          omega
      exact hhas.ord_eq_zero hev
    rw [Place.ord_mul _ ?_ haeval0, ord_nodeTgt_ssPolyBar', hval, add_zero]
    rw [ssPolyBar_eq_prod']; exact Finset.prod_ne_zero_iff.mpr fun x _ => jBar_sub_algebraMap_ne_zero' A _

  have htight : ∀ (m : Fin r), 1 ≤ (m : ℕ) → (P m).natDegree ≤ 1 → (P m).eval (ssValue Γ e) ≠ 0 →
      hasseExp Φ.toFamData m = jWidth (ssValue Γ e) →
      ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩), (nodeSrc Γ e).ord f = -1 := by
    intro m hm1 hdm hev hmw
    have hord := hordP m hm1 hdm e hev
    obtain ⟨f, hf, hfo⟩ := exists_mem_span_ord_nodeSrc_eq_neg_of_combination' p A hA Γ Δ Φ hint hLI hintI P
      (fun l' hl' => (hP l' hl').2) (hasseExp Φ.toFamData m) (by have := one_le_hasseExp p A hA Γ Φ m hm1; omega)
      (Pi.single m 1)
      (fun l' hl' => by
        by_cases h : l' = m
        · subst h; rfl
        · rw [Pi.single_eq_of_ne h] at hl'; exact (hl' rfl).elim)
      ⟨m, by rw [Pi.single_eq_same]; exact one_ne_zero⟩ (P m)
      (by rw [Finset.sum_eq_single m (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
        (fun h => (h (Finset.mem_univ m)).elim), Pi.single_eq_same, one_smul]) e
      (by rw [hord, mul_one]; exact_mod_cast hmw)
    exact ⟨f, hf, by rw [hfo, hord]⟩

  have hbound : ∀ (m : Fin r), 1 ≤ (m : ℕ) → (P m).natDegree ≤ 1 → ∀ e', (P m).eval (ssValue Γ e') ≠ 0 →
      hasseExp Φ.toFamData m ≤ jWidth (ssValue Γ e') := by
    intro m hm1 hdm e' hev
    have hord := hordP m hm1 hdm e' hev
    have hres_eq := (hP m hm1).2
    have h := hasseExp_le_jWidth_mul_ord_nodeTgt' p A hA Γ Δ Φ hintI e' m
      (by show 0 ≤ (charLGeomPlaceOfPoint _ _).ord _; rw [hres_eq, hord]; exact zero_le_one)
    have h2 : (nodeTgt Γ e').ord ((infChart Γ).residue ⟨goodFamily Φ m, hintI m⟩) = 1 := by
      show (charLGeomPlaceOfPoint _ _).ord _ = 1; rw [hres_eq, hord]
    rw [h2, mul_one] at h; exact_mod_cast h

  have hw23 : jWidth (ssValue Γ e) = 2 ∨ jWidth (ssValue Γ e) = 3 := by
    rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h
    · exact absurd h (hwide e)
    · exact Or.inl h
    · exact Or.inr h
  rcases hw23 with hw2' | hw3'
  ·
    rw [hw2']
    have hv : hasseExp Φ.toFamData l / 2 = 1 := by rcases hnl with h | h <;> rw [h]
    rw [hv]
    show ∃ f ∈ _, (nodeSrc Γ e).ord f = -1
    by_cases hevl : (P l).eval (ssValue Γ e) = 0
    ·
      have hevl' : (P l').eval (ssValue Γ e) ≠ 0 := fun h => hnotboth _ ⟨hevl, h⟩
      have h2 := hbound l' hl'1 hdegl' e hevl'
      rw [hw2'] at h2
      have h1 := one_le_hasseExp p A hA Γ Φ l' hl'1
      have hn2 : hasseExp Φ.toFamData l' = 2 := by have := hne1 l' hl'1; omega
      exact htight l' hl'1 hdegl' hevl' (by rw [hn2, hw2'])
    ·
      have h2 := hbound l hl1 hdegl e hevl
      rw [hw2'] at h2
      have hn2 : hasseExp Φ.toFamData l = 2 := by omega
      exact htight l hl1 hdegl hevl (by rw [hn2, hw2'])
  ·
    rw [hw3']
    rcases hnl with hn2 | hn3'
    · rw [hn2]; simpa using C0 e
    · rw [hn3']
      show ∃ f ∈ _, (nodeSrc Γ e).ord f = -1

      obtain ⟨e', he'⟩ : ∃ e' : Fin (mAnnuli p), e' ≠ e := by
        have : 1 < Fintype.card (Fin (mAnnuli p)) := by rw [Fintype.card_fin, hm]; omega
        obtain ⟨e', he'⟩ := Fintype.exists_ne_of_one_lt_card this e
        exact ⟨e', he'⟩
      have hw_e' : jWidth (ssValue Γ e') = 2 := by

        rcases jWidth_eq_one_or (ssValue Γ e') with h | h | h
        · exact absurd h (hwide e')
        · exact h
        · exfalso
          have h0 : ssValue Γ e = 0 := by
            by_contra hne; rw [jWidth_eq_ite] at hw3'; rw [if_neg hne] at hw3'; split_ifs at hw3' <;> omega
          have h0' : ssValue Γ e' = 0 := by
            by_contra hne; rw [jWidth_eq_ite] at h; rw [if_neg hne] at h; split_ifs at h <;> omega
          exact he' (ssValue_injective Γ (h0'.trans h0.symm))
      have hevl' : (P l).eval (ssValue Γ e') = 0 := by
        by_contra hne
        have := hbound l hl1 hdegl e' hne
        rw [hw_e'] at this; omega
      have hevl : (P l).eval (ssValue Γ e) ≠ 0 := by
        intro h0

        have hPl0 : P l ≠ 0 := hli.ne_zero ⟨l, hl1⟩
        have e1 := hfactor (P l) hdegl _ hevl'
        have : (P l).eval (ssValue Γ e) = (P l).leadingCoeff * (ssValue Γ e - ssValue Γ e') := by
          conv_lhs => rw [e1]
          simp
        rw [this] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · exact hPl0 (Polynomial.leadingCoeff_eq_zero.mp h)
        · exact he' (ssValue_injective Γ (sub_eq_zero.mp h)).symm
      exact htight l hl1 hdegl hevl (by rw [hn3', hw3'])

end CTightSmall

section CTightFinal

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA Δ in

theorem exists_mem_span_zeroChart_residue_ord_nodeSrc_eq_neg_hasseExp_div_jWidth' (hp5 : 5 ≤ p)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e : Fin (mAnnuli p)) (l : Fin r) :
    ∃ f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l' : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l', hint l'⟩),
      (nodeSrc Γ e).ord f = -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ) := by
  classical
  by_cases hp13 : 13 ≤ p
  · exact exists_mem_span_zeroChart_residue_ord_nodeSrc_eq_neg_hasseExp_div_jWidth_of_thirteen_le' p A hA Γ Δ Φ
      hp13 hint hLI e l
  push_neg at hp13
  have hp : p.Prime := Fact.out
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 := by
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by decide)
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact absurd hp (by decide)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hp (by decide)
  rcases hcases with rfl | rfl | rfl
  · exact exists_mem_span_ord_nodeSrc_eq_of_mAnnuli_eq_one' 5 A hA Γ Δ Φ (by decide) hint hLI e l
  · exact exists_mem_span_ord_nodeSrc_eq_of_mAnnuli_eq_one' 7 A hA Γ Δ Φ (by decide) hint hLI e l
  · haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
    refine exists_mem_span_ord_nodeSrc_eq_of_mAnnuli_eq_two_of_forall_wide' 11 A hA Γ Δ Φ (by decide) (by norm_num)
      ?_ hint hLI e l
    intro e'
    have hmem := ssValue_mem_ssJSet Γ e'
    have hss : ssJSet 11 (ResidueField ↥A) = ssJSetHasse 11 (ResidueField ↥A) :=
      ssJSet_eq_ssJSetHasse 11 (by decide) (ResidueField ↥A)
    have h0 : (0 : ResidueField ↥A) ∈ ssJSet 11 (ResidueField ↥A) := by
      rw [hss]; exact (zero_mem_ssJSetHasse_iff 11 (by norm_num) (ResidueField ↥A)).mpr (by decide)
    have h1728 : (1728 : ResidueField ↥A) ∈ ssJSet 11 (ResidueField ↥A) := by
      rw [hss]; exact (ofNat1728_mem_ssJSetHasse_iff 11 (by norm_num) (ResidueField ↥A)).mpr (by decide)
    have hne : (1728 : ResidueField ↥A) ≠ 0 := by
      intro h
      have h' : ((1728 : ℕ) : ResidueField ↥A) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff (ResidueField ↥A) 11] at h'
      norm_num at h'
    have hcard : Γ.hfin.toFinset.card = 2 := by rw [Γ.hcard]; decide
    have hsub : ({0, 1728} : Finset (ResidueField ↥A)) ⊆ Γ.hfin.toFinset := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Set.Finite.mem_toFinset]
      rcases hx with rfl | rfl
      · exact h0
      · exact h1728
    have heq : ({0, 1728} : Finset (ResidueField ↥A)) = Γ.hfin.toFinset :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_pair hne.symm])
    have hx : ssValue Γ e' ∈ ({0, 1728} : Finset (ResidueField ↥A)) := by
      rw [heq, Set.Finite.mem_toFinset]; exact hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · rw [jWidth_of_eq_zero h]; decide
    · rw [jWidth_of_eq_1728 h (by rw [h]; exact hne)]; decide

end CTightFinal

end ModularCurve.MultCovering

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul.ModularCurve.MultCovering in
theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e : Fin (mAnnuli p)) (h : ↥(modularFunctionFieldBar (1 * p))) (hC : h ∈ (infChart Γ).integers)
    (hres : (infChart Γ).residue ⟨h, hC⟩ ≠ 0)
    (hfpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W.ord h < 0 → W = cuspInftyBar (1 * p))
    (n : ℕ) (hC' : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * h
      ∈ (zeroChart Γ).integers)
    (hres' : (zeroChart Γ).residue ⟨_, hC'⟩ ≠ 0)
    (hna : (n : ℤ) = (jWidth (ssValue Γ e) : ℤ) * (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩)) :
    (∀ Q ∈ (Δ.annIn e).dom, Q.ord h = 0) ∧
      (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨_, hC'⟩) = - (nodeTgt Γ e).ord ((infChart Γ).residue ⟨h, hC⟩) :=
  ModularCurve.MultCovering.ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul' p A hA Γ Δ e h hC hres hfpole n hC' hres' hna

end S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul
end P2MW
export P2MW.S_ModularCurve_MultCovering_ord_nodeSrc_zeroChart_residue_eq_neg_ord_nodeTgt_of_hasseExp_eq_jWidth_mul (solution)
