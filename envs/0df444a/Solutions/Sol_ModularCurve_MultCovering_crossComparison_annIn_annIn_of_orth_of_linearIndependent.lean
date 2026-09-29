-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e3fc042c-20b5-501a-9903-aa4419263ce8

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_AlgebraicCurve_Annulus_exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_exists_unimodular_famData_wideCertificates
import Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_toFamData_eq_of_bifiltered
import Theorems.Thm_ModularCurve_MultCovering_compConst_eq_of_t_eq_sum
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_deep_of_zeroFree
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_outer
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_leadingTerms
import Theorems.Thm_ModularCurve_MultCovering_ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_two_of_thirteen_le
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_MultCovering_forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
import Theorems.Thm_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one
import Theorems.Thm_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase"
p2m_attr_erase "instance" "instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_unimodular_famData_wideCertificates MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.compConst_eq_of_t_eq_sum MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer MultCovering.crossComparison_annIn_annIn_of_leadingTerms MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one MultCovering.hasseExp_le_two_of_thirteen_le MultCovering.one_le_hasseExp MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one MultCovering.tangentDet_ne_zero_of_hasseExp_two"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_unimodular_famData_wideCertificates exists_famCtx_toFamData_eq_of_bifiltered compConst_eq_of_t_eq_sum crossComparison_annIn_annIn_of_jWidth_eq_one crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer crossComparison_annIn_annIn_of_leadingTerms ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one hasseExp_le_two_of_thirteen_le one_le_hasseExp forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth exists_ne_hasseExp_eq_two_of_jWidth_ne_one tangentDet_ne_zero_of_hasseExp_two"
p2m_open "ModularCurve.MultCovering ModularCurve"

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

section MoreHelpers

theorem evalAt_sub_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_add_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem mem_maximalIdeal_of_abv_lt_one_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : μ x < 1) : (⟨x, hx⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have hinv : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x⁻¹ := by
    have h1 := congrArg (fun t : ↥A => (t : AlgebraicClosure ℚ)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxinv : μ x⁻¹ ≤ 1 := (hμA _).1 (hinv ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2)
  rw [map_inv₀] at hxinv
  have : 1 < (μ x)⁻¹ := (one_lt_inv₀ (μ.pos hx0)).2 h
  linarith

theorem chart_residue_algebraMap_eq_zero_D
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

end MoreHelpers

section FamilyFacts
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)

theorem goodFamily_ne_zero' (i : Fin r) : goodFamily Φ i ≠ 0 := Φ.t_basis.1.ne_zero i

theorem goodFamily_mem_riemannRochSpace' (i : Fin r) : goodFamily Φ i ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← Φ.t_basis.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem goodFamilyZero_eq_inv_mul' (l : Fin r) :
    goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * goodFamily Φ l := rfl

theorem goodFamily_mem_of_ne_cuspInftyBar'
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : w ≠ cuspInftyBar (1 * p)) (i : Fin r) :
    0 ≤ w.ord (goodFamily Φ i) ∧ goodFamily Φ i ∈ w.toValuationSubring := by
  have h0 : goodFamily Φ i ≠ 0 := goodFamily_ne_zero' Φ i
  have hmem := (mem_riemannRochSpace_iff.mp (goodFamily_mem_riemannRochSpace' Φ i)) w
  have hD : (embDivisor (1 * p)) w = 0 := by simp [embDivisor, hw]
  rcases hmem with h' | h'
  · exact absurd h' h0
  · rw [hD, neg_zero] at h'
    exact ⟨h', w.mem_of_ord_nonneg h0 h'⟩

end FamilyFacts

section CtxFacts
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
  (Γ : ChartCtx p A) (Δ : AnnCtx Γ)

theorem modulus_dvd' (e : Fin (mAnnuli p)) : ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  have hw : jWidth (ssValue Γ e) ≤ 3 := by
    unfold jWidth; split_ifs <;> norm_num
  refine ⟨(p : AlgebraicClosure ℚ) ^ (3 - jWidth (ssValue Γ e)), pow_mem (natCast_mem A p) _, ?_⟩
  have hm : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  rw [hm, ← pow_add, show modulusExp = 3 from rfl, Nat.add_sub_cancel' hw]

end CtxFacts

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_unimodular_famData_wideCertificates MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.compConst_eq_of_t_eq_sum MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer MultCovering.crossComparison_annIn_annIn_of_leadingTerms MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one MultCovering.hasseExp_le_two_of_thirteen_le MultCovering.one_le_hasseExp MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one MultCovering.tangentDet_ne_zero_of_hasseExp_two"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_unimodular_famData_wideCertificates exists_famCtx_toFamData_eq_of_bifiltered compConst_eq_of_t_eq_sum crossComparison_annIn_annIn_of_jWidth_eq_one crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer crossComparison_annIn_annIn_of_leadingTerms ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one hasseExp_le_two_of_thirteen_le one_le_hasseExp forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth exists_ne_hasseExp_eq_two_of_jWidth_ne_one tangentDet_ne_zero_of_hasseExp_two"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

theorem annOut_wide' (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
        μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  intro μ hμA
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA
  refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
  have key : ∀ Q ∈ (Δ.annIn e).dom,
      μ (Q.evalAt (Δ.annOut e).param) * μ (Q.evalAt (Δ.annIn e).param)
        = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) := by
    intro Q hQ
    obtain ⟨hrat, hzin, -, hz0, -⟩ := (Δ.annIn e).mem_dom Q hQ
    obtain ⟨-, hzout, -⟩ := (Δ.annOut e).mem_dom Q (hdom ▸ hQ)
    rw [← map_mul, ← evalAt_mul_D Q hrat hzout hzin, htwo, evalAt_algebraMap_D]
  intro heq
  apply hne
  have h1 := key Q₁ hQ₁
  have h2 := key Q₂ hQ₂
  rw [heq] at h1
  have h12 := h1.trans h2.symm
  have hne0 : μ (Q₂.evalAt (Δ.annOut e).param) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (μ.pos hmod0).ne' h2.symm
  exact mul_left_cancel₀ hne0 h12

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_unimodular_famData_wideCertificates MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.compConst_eq_of_t_eq_sum MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer MultCovering.crossComparison_annIn_annIn_of_leadingTerms MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one MultCovering.hasseExp_le_two_of_thirteen_le MultCovering.one_le_hasseExp MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one MultCovering.tangentDet_ne_zero_of_hasseExp_two"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_unimodular_famData_wideCertificates exists_famCtx_toFamData_eq_of_bifiltered compConst_eq_of_t_eq_sum crossComparison_annIn_annIn_of_jWidth_eq_one crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer crossComparison_annIn_annIn_of_leadingTerms ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one hasseExp_le_two_of_thirteen_le one_le_hasseExp forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth exists_ne_hasseExp_eq_two_of_jWidth_ne_one tangentDet_ne_zero_of_hasseExp_two"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

section P2Helpers

theorem abv_sub_eq_max_of_ne_D {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    {a b : K} (h : μ a ≠ μ b) : μ (a - b) = max (μ a) (μ b) := by
  have hsub : ∀ u v : K, μ (u - v) ≤ max (μ u) (μ v) := by
    intro u v; rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ v]; exact hμ _ _
  refine le_antisymm (hsub a b) ?_
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [max_eq_right hlt.le]
    have h1 := hμ (b - a) a
    rw [sub_add_cancel] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · rw [← neg_sub, AbsoluteValue.map_neg] at h2; exact h2
    · exact absurd h2 (not_le.2 hlt)
  · rw [max_eq_left hlt.le]
    have h1 := hμ (a - b) b
    rw [sub_add_cancel] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 hlt)

theorem abv_sub_le_max_D {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (a b : K) : μ (a - b) ≤ max (μ a) (μ b) := by
  rw [sub_eq_add_neg, ← AbsoluteValue.map_neg μ b]; exact hμ _ _

theorem abv_eq_one_of_isUnit_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (hu : IsUnit (⟨x, hx⟩ : ↥A)) : μ x = 1 := by
  refine le_antisymm ((hμA x).1 hx) ?_
  have hinv : x⁻¹ ∈ A := vs_inv_mem_of_isUnit_D hx hu
  have hx0 : x ≠ 0 := by
    intro h0; obtain ⟨u, hu'⟩ := hu
    have : (u : ↥A) = 0 := by rw [hu']; exact Subtype.ext h0
    exact u.ne_zero this
  have h1 : μ x⁻¹ ≤ 1 := (hμA _).1 hinv
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (μ.pos hx0)).1 h1

theorem isUnit_of_abv_eq_one_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : μ x = 1) : IsUnit (⟨x, hx⟩ : ↥A) := by
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hinv : x⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem abv_lt_one_of_residue_eq_zero_D {A : ValuationSubring (AlgebraicClosure ℚ)}
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (h : IsLocalRing.residue ↥A ⟨x, hx⟩ = 0) : μ x < 1 :=
  abv_lt_one_of_mem_maximalIdeal_D μ hμA ((IsLocalRing.residue_eq_zero_iff _).1 h)

theorem evalAt_eq_zero_of_ord_ne_zero_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (h : v.ord f ≠ 0) : v.evalAt f = 0 := by
  by_contra hne
  exact h (ord_eq_zero_of_evalAt_ne_zero_D v hf hne)

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

theorem nodeTgt_isRational_D (Γ : ChartCtx p A) (ε : Fin (mAnnuli p)) : (nodeTgt Γ ε).IsRational := by
  apply isRational_of_deg_eq_one
  exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ ε)

theorem nodeSrc_isRational_D (Γ : ChartCtx p A) (ε : Fin (mAnnuli p)) : (nodeSrc Γ ε).IsRational := by
  apply isRational_of_deg_eq_one
  exact ModularCurve.deg_charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ ε ^ p)

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem engine_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hβ : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ Q ∈ (Δ.annIn ε).dom,
      μ (Q.evalAt (Δ.annOut ε).param) = μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l ∧
      (∀ X ∈ (Δ.annIn ε).dom, X.ord (goodFamily Φ l) ≠ 0 → X = Q) ∧
      (∃ hq : Q.evalAt (Δ.annOut ε).param * ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l)⁻¹ ∈ A,
        IsUnit (⟨_, hq⟩ : ↥A) ∧
        IsLocalRing.residue ↥A ⟨_, hq⟩
          = -((nodeSrc Γ ε).evalAt ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩))
              * ((nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
                  * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹))⁻¹) ∧
      ∀ X ∈ (Δ.annIn ε).dom,
        ∃ hu : X.evalAt (goodFamily Φ l * ((Δ.annOut ε).param
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹) ∈ A,
          IsUnit (⟨_, hu⟩ : ↥A) ∧
          IsLocalRing.residue ↥A ⟨_, hu⟩
            = (nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
                * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹) ∧
          X.evalAt (goodFamily Φ l)
            = X.evalAt (goodFamily Φ l * ((Δ.annOut ε).param
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹)
              * (X.evalAt (Δ.annOut ε).param - Q.evalAt (Δ.annOut ε).param) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set n := hasseExp Φ.toFamData l with hn
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ n with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
  set zo := (Δ.annOut ε).param with hzo
  have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
  have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
    intro h0
    have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  have hscaled : goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hint0
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
  have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint0⟩ := Subtype.ext hscaled.symm
  have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
  have hord't : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨_, hC't⟩) = 0 := by rw [e2]; exact hβ
  have hrow : ∀ X ∈ (Δ.annIn ε).dom, t l ∈ X.toValuationSubring :=
    fun X hX => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε X hX l hl).1
  have hpole : ∀ X ∈ (Δ.annOut ε).dom, 0 ≤ X.ord (t l) := fun X hX => X.ord_nonneg_of_mem (hrow X (hdom ▸ hX))
  obtain ⟨Q, hQdom, hordQ, hordP, hμQ, ⟨hq, hqunit, hqres⟩, hfac⟩ :=
    AlgebraicCurve.Annulus.exists_unique_zero_and_isUnit_evalAt_div_param_sub_of_ord_residue_eq_one μ hμA
      (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
      (nodeTgt_isRational_D Γ ε) (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε) (nodeSrc_isRational_D Γ ε)
      hwide (t l) hint hrest hord c₁ hc₁0 hc₁A hC't hres't hord't hpole hz
  refine ⟨Q, hdom ▸ hQdom, by rw [hμQ, hc₁, map_pow], ?_, ⟨hq, hqunit, ?_⟩, ?_⟩
  · intro X hX hXord
    by_contra hXQ
    exact hXord (hordP X (hdom ▸ hX) hXQ)
  · rw [hqres, e2]
  · intro X hX
    have hXout : X ∈ (Δ.annOut ε).dom := hdom ▸ hX
    obtain ⟨hu, huunit, hures⟩ := hfac X hXout
    refine ⟨hu, huunit, hures, ?_⟩
    obtain ⟨hXrat, hzoX, -, hzoX0, -⟩ := (Δ.annOut ε).mem_dom X hXout
    have htX : t l ∈ X.toValuationSubring := hrow X hX
    by_cases hXQ : X = Q
    · subst hXQ
      have hev : X.evalAt (t l) = 0 := evalAt_eq_zero_of_ord_ne_zero_D X htX (by rw [hordQ]; exact one_ne_zero)
      rw [hev, sub_self, mul_zero]
    · have hwX : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param) ∈ X.toValuationSubring :=
        sub_mem hzoX (X.algebraMap_mem' _)
      have hwev : X.evalAt (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param)) = X.evalAt zo - Q.evalAt (Δ.annOut ε).param := by
        rw [evalAt_sub_D X hXrat hzoX (X.algebraMap_mem' _), evalAt_algebraMap_D]
      have hwne : X.evalAt zo - Q.evalAt (Δ.annOut ε).param ≠ 0 := by
        rw [sub_ne_zero]
        intro h1; apply hXQ
        obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := (Δ.annOut ε).mem_dom Q hQdom
        obtain ⟨P₀, -, huniq⟩ := (Δ.annOut ε).existsUnique_evalAt_eq ⟨Q.evalAt (Δ.annOut ε).param, haA⟩ ha𝔪 ha0 hm
        exact (huniq X ⟨hXout, h1⟩).trans (huniq Q ⟨hQdom, rfl⟩).symm
      have hev0 : X.evalAt (0 : modularFunctionFieldBar (1 * p)) = 0 := by
        rw [X.evalAt_of_mem (zero_mem _)]
        have : (⟨(0 : modularFunctionFieldBar (1 * p)), zero_mem _⟩ : X.toValuationSubring) = 0 := rfl
        rw [this, map_zero, ← map_zero (algebraMap (AlgebraicClosure ℚ) X.ResidueField), X.residueInv_algebraMap]
      have hw0 : zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param) ≠ 0 := by
        intro h0; apply hwne; rw [← hwev, h0, hev0]
      have hordw : X.ord (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param)) = 0 :=
        ord_eq_zero_of_evalAt_ne_zero_D X hwX (by rw [hwev]; exact hwne)
      have hwinvX : (zo - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (Q.evalAt (Δ.annOut ε).param))⁻¹ ∈ X.toValuationSubring :=
        X.mem_of_ord_nonneg (inv_ne_zero hw0) (by rw [Place.ord_inv, hordw]; norm_num)
      rw [← hwev, ← evalAt_mul_D X hXrat (mul_mem htX hwinvX) hwX, inv_mul_cancel_right₀ hw0]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem outerUnit_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (X : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hX : X ∈ (Δ.annIn ε).dom)
    (hout : ∀ Y ∈ (Δ.annIn ε).dom, Y.ord (goodFamily Φ l) ≠ 0 →
      μ (Y.evalAt (Δ.annOut ε).param) < μ (X.evalAt (Δ.annOut ε).param)) :
    ∃ hmem : X.evalAt (goodFamily Φ l) * (X.evalAt (Δ.annOut ε).param)⁻¹ ∈ A,
      IsUnit (⟨_, hmem⟩ : ↥A) ∧
      IsLocalRing.residue ↥A ⟨_, hmem⟩
        = (nodeTgt Γ ε).evalAt ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩
            * ((infChart Γ).residue ⟨(Δ.annOut ε).param, hz⟩)⁻¹) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set t := goodFamily Φ with ht
  set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc₁
  have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
  have hc₁A : c₁ ∈ A := pow_mem hpA _
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
  set zo := (Δ.annOut ε).param with hzo
  have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
    rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
  have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
  have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
    intro h0
    have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  have hscaled : goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
  have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
    rw [← hscaled]; exact hint0
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
  have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
  have hrow : ∀ Y ∈ (Δ.annIn ε).dom, t l ∈ Y.toValuationSubring :=
    fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Y hY l hl).1
  have hpole : ∀ Y ∈ (Δ.annOut ε).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
  have hout' : ∀ Y ∈ (Δ.annOut ε).dom, Y.ord (t l) ≠ 0 → μ (Y.evalAt zo) < μ (X.evalAt zo) :=
    fun Y hY hYord => hout Y (hdom ▸ hY) hYord
  obtain ⟨hmem, hunit, hres⟩ :=
    AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt μ hμA
      (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
      (nodeTgt_isRational_D Γ ε) (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε)
      hwide (t l) hint hrest c₁ hc₁0 hc₁A hC't hres't hpole hz X (hdom ▸ hX) hout'
  have eA : X.evalAt (t l) * (X.evalAt zo) ^ (-((nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩)))
      = X.evalAt (t l) * (X.evalAt zo)⁻¹ := by rw [hord]; simp
  have eB : (infChart Γ).residue ⟨t l, hint⟩ * ((infChart Γ).residue ⟨zo, hz⟩) ^ (-((nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩)))
      = (infChart Γ).residue ⟨t l, hint⟩ * ((infChart Γ).residue ⟨zo, hz⟩)⁻¹ := by rw [hord]; simp
  have hmem' : X.evalAt (t l) * (X.evalAt zo)⁻¹ ∈ A := eA ▸ hmem
  have e3 : (⟨_, hmem'⟩ : ↥A) = ⟨_, hmem⟩ := Subtype.ext eA.symm
  refine ⟨hmem', by rw [e3]; exact hunit, ?_⟩
  rw [e3, hres, eB]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem zerosDepth_D (hA : A.LiesOverPrime p) (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (ε : Fin (mAnnuli p)) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : goodFamily Φ l ∈ (infChart Γ).integers) (hint0 : goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hz : (Δ.annOut ε).param ∈ (infChart Γ).integers)
    (hord : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint⟩) = 1)
    (hβle : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) ≤ 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    (∀ X ∈ (Δ.annIn ε).dom, X.ord (goodFamily Φ l) ≠ 0 →
        μ (X.evalAt (Δ.annOut ε).param) = μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l) ∧
    (∀ X ∈ (Δ.annIn ε).dom, μ (X.evalAt (goodFamily Φ l))
        ≤ max (μ (X.evalAt (Δ.annOut ε).param)) (μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  by_cases hβ0 : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) = 0
  · obtain ⟨Q, hQ, hμQ, hzeros, -, hfac⟩ := engine_D hA Γ Δ Φ ε l hl hint hint0 hz hord hβ0 μ hμA
    refine ⟨fun X hX hXord => by rw [hzeros X hX hXord]; exact hμQ, fun X hX => ?_⟩
    obtain ⟨hu, huunit, -, hmul⟩ := hfac X hX
    rw [hmul, map_mul, abv_eq_one_of_isUnit_D μ hμA hu huunit, one_mul (μ _), ← hμQ]
    exact abv_sub_le_max_D μ hμ _ _
  ·
    have hβneg : (nodeSrc Γ ε).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0⟩) < 0 :=
      lt_of_le_of_ne hβle hβ0
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
    set t := goodFamily Φ with ht
    set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l with hc₁
    have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
    have hc₁A : c₁ ∈ A := pow_mem hpA _
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
    set zo := (Δ.annOut ε).param with hzo
    have hmod0' : ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : (Δ.annIn ε).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((Δ.annOut ε).modulus : AlgebraicClosure ℚ) := by
      rw [show (Δ.annIn ε).param * zo = zo * (Δ.annIn ε).param from mul_comm _ _, hzo, htwo, hmod]
    have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
    have hrest : (infChart Γ).residue ⟨t l, hint⟩ ≠ 0 := by
      intro h0
      have h1 : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
      rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
    have hscaled : goodFamilyZero Φ.toFamData l
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
    have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
      rw [← hscaled]; exact hint0
    obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
    have e1 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hintZ l⟩ := Subtype.ext hscaled.symm
    have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint0⟩ := Subtype.ext hscaled.symm
    have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by rw [e1]; exact hresZ l
    have hrow : ∀ Y ∈ (Δ.annIn ε).dom, t l ∈ Y.toValuationSubring :=
      fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Y hY l hl).1
    have hpole : ∀ Y ∈ (Δ.annOut ε).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
    obtain ⟨D, hD0, hDsupp, hDord, hdeg, -⟩ :=
      AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
        (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ ε) (Δ.attached_tgt ε)
        (zeroChart Γ) (nodeSrc Γ ε) (Δ.attached_src ε) hwide (t l) hint hrest c₁ hc₁0 hc₁A hC't hres't hpole
    have hordt : (nodeTgt Γ ε).ord ((infChart Γ).residue ⟨t l, hint⟩) = 1 := hord
    rw [hordt, e2] at hdeg
    have hsum0 : (D.sum fun _ m => m) ≤ 0 := by rw [hdeg]; omega
    have hDzero : ∀ Y, D Y = 0 := by
      intro Y
      by_contra hne
      have hpos : 0 < D Y := lt_of_le_of_ne (hD0 Y) (Ne.symm hne)
      have hle : D Y ≤ D.sum fun _ m => m := by
        rw [Finsupp.sum]
        exact Finset.single_le_sum (fun Y' _ => hD0 Y') (Finsupp.mem_support_iff.2 hne)
      omega
    have hzf : ∀ Y ∈ (Δ.annIn ε).dom, Y.ord (t l) = 0 := fun Y hY => by rw [← hDord Y (hdom ▸ hY), hDzero]
    refine ⟨fun X hX hXord => absurd (hzf X hX) hXord, fun X hX => ?_⟩
    obtain ⟨hmem, hunit, -⟩ := outerUnit_D hA Γ Δ Φ ε l hl hint hint0 hz hord μ hμA X hX
      (fun Y hY hYord => absurd (hzf Y hY) hYord)
    obtain ⟨-, hzoX, -, hzoX0, -⟩ := (Δ.annOut ε).mem_dom X (hdom ▸ hX)
    have h1 : μ (X.evalAt (t l) * (X.evalAt zo)⁻¹) = 1 := abv_eq_one_of_isUnit_D μ hμA hmem hunit
    rw [map_mul, map_inv₀, mul_inv_eq_one₀ (μ.pos hzoX0).ne'] at h1
    rw [h1]; exact le_max_left _ _

end P2Helpers
end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar deg_charLGeomPlaceOfPoint jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional MultCovering.exists_unimodular_famData_wideCertificates MultCovering.exists_famCtx_toFamData_eq_of_bifiltered MultCovering.compConst_eq_of_t_eq_sum MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree MultCovering.crossComparison_annIn_annIn_of_outer MultCovering.crossComparison_annIn_annIn_of_leadingTerms MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one MultCovering.hasseExp_le_two_of_thirteen_le MultCovering.one_le_hasseExp MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one MultCovering.tangentDet_ne_zero_of_hasseExp_two"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero FamCtx goodFamily compConst zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom exists_unimodular_famData_wideCertificates exists_famCtx_toFamData_eq_of_bifiltered compConst_eq_of_t_eq_sum crossComparison_annIn_annIn_of_jWidth_eq_one crossComparison_annIn_annIn_of_deep_of_zeroFree crossComparison_annIn_annIn_of_outer crossComparison_annIn_annIn_of_leadingTerms ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one hasseExp_le_two_of_thirteen_le one_le_hasseExp forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth exists_ne_hasseExp_eq_two_of_jWidth_ne_one tangentDet_ne_zero_of_hasseExp_two"
p2m_open "ModularCurve.MultCovering ModularCurve"
open AlgebraicCurve IsLocalRing

theorem prox_symm_D {K : Type*} [Field K] {r : ℕ} (μ : AbsoluteValue K ℝ) (x y : Fin r → K) :
    prox μ x y = prox μ y x := by
  unfold prox
  have h : (fun q : Fin r × Fin r => μ (y q.1 * x q.2 - y q.2 * x q.1))
      = fun q : Fin r × Fin r => μ (x q.1 * y q.2 - x q.2 * y q.1) := by
    funext q
    rw [show y q.1 * x q.2 - y q.2 * x q.1 = -(x q.1 * y q.2 - x q.2 * y q.1) by ring, AbsoluteValue.map_neg]
  simp only [h]
  ring

end ModularCurve.MultCovering

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in

theorem solution (p : ℕ) [Fact p.Prime]
    (hp13 : 13 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hAd : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
        LinearIndependent (IsLocalRing.ResidueField ↥A)
          (fun l => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := le_trans (by norm_num) hp13
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have h1728 : (1728 : IsLocalRing.ResidueField ↥A) ≠ 0 := by
    intro h
    have hdvd : p ∣ 1728 := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) p 1728).1 (by exact_mod_cast h)
    have h' : p ∣ 2 ^ 6 * 3 ^ 3 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega
  have hwide_iff : ∀ e₀ : Fin (mAnnuli p), jWidth (ssValue Γ e₀) ≠ 1 ↔ (ssValue Γ e₀ = 0 ∨ ssValue Γ e₀ = 1728) := by
    intro e₀
    rcases eq_or_ne (ssValue Γ e₀) 0 with h0 | h0
    · rw [jWidth_of_eq_zero h0]; simp [h0]
    rcases eq_or_ne (ssValue Γ e₀) 1728 with h1 | h1
    · rw [jWidth_of_eq_1728 h1 h0]; simp [h1]
    · rw [jWidth_of_ne h0 h1]; simp [h0, h1]
  have hw_cases : ∀ e₀ : Fin (mAnnuli p), jWidth (ssValue Γ e₀) = 1 ∨ jWidth (ssValue Γ e₀) = 2 ∨ jWidth (ssValue Γ e₀) = 3 := by
    intro e₀
    rcases eq_or_ne (ssValue Γ e₀) 0 with h0 | h0
    · exact Or.inr (Or.inr (jWidth_of_eq_zero h0))
    rcases eq_or_ne (ssValue Γ e₀) 1728 with h1 | h1
    · exact Or.inr (Or.inl (jWidth_of_eq_1728 h1 h0))
    · exact Or.inl (jWidth_of_ne h0 h1)

  obtain ⟨hint, hLI⟩ := hAd A hA Γ
  obtain ⟨U, D', hint', hintI', hUunit, hU, hUinv, hU0, htRat, ht, hexp, hgfz, hLI', hexC1, hexC2, hresI', hatt0, hIwide, hIone, hItwo, hSEP2, hUNR⟩ :=
    ModularCurve.MultCovering.exists_unimodular_famData_wideCertificates p hp13 A hA Γ Δ Φ hint hLI
  obtain ⟨Φ', hΦ'⟩ := ModularCurve.MultCovering.exists_famCtx_toFamData_eq_of_bifiltered p Φ horthInf horthZero
    U hUunit hU hUinv hU0 D' htRat ht hexp
  subst hΦ'
  have hC1 : ∃ l₁ : Fin r, 1 ≤ (l₁ : ℕ) ∧ hasseExp Φ.toFamData l₁ = 1 := hexC1
  have hC2two : ∀ e₁ e₂ : Fin (mAnnuli p), e₁ ≠ e₂ → jWidth (ssValue Γ e₁) ≠ 1 → jWidth (ssValue Γ e₂) ≠ 1 →
      ∃ l₂ l₃ : Fin r, l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
        hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 2 :=
    ModularCurve.MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one p hp13 A hA Γ Δ Φ hint hLI
  have hexp12 : ∀ l : Fin r, 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 1 ∨ hasseExp Φ.toFamData l = 2 := by
    intro l hl
    have h1 := ModularCurve.MultCovering.one_le_hasseExp p A hA Γ Φ l hl
    have h2 := ModularCurve.MultCovering.hasseExp_le_two_of_thirteen_le p hp13 A hA Γ Δ Φ l
    omega

  have hINV : compConst Φ' s hs = compConst Φ s hs := by
    refine ModularCurve.MultCovering.compConst_eq_of_t_eq_sum p Φ Φ' s hs U hUunit ?_ ?_ ht
    · intro i j; rcases hU i j with h | h
      · exact Or.inl ((le_max_left _ _).trans h)
      · exact Or.inr h
    · intro i j; rcases hUinv i j with h | h
      · exact Or.inl ((le_max_left _ _).trans h)
      · exact Or.inr h
  rw [← hINV]

  have hβle : ∀ (e₀ : Fin (mAnnuli p)) (l : Fin r),
      (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ'.toFamData l, hint' l⟩) ≤ 0 := by
    intro e₀ l; rw [hatt0]
    have : (0 : ℤ) ≤ ((hasseExp Φ.toFamData l / jWidth (ssValue Γ e₀) : ℕ) : ℤ) := Int.natCast_nonneg _
    omega
  have hβeq : ∀ (e₀ : Fin (mAnnuli p)) (l : Fin r), hasseExp Φ.toFamData l < jWidth (ssValue Γ e₀) →
      (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ'.toFamData l, hint' l⟩) = 0 := by
    intro e₀ l hlt; rw [hatt0, Nat.div_eq_of_lt hlt]; simp

  have hzinf : ∀ e₀ : Fin (mAnnuli p), (Δ.annOut e₀).param ∈ (infChart Γ).integers := by
    intro e₀; obtain ⟨-, hzoC, -, -⟩ := Δ.attached_tgt e₀; exact hzoC

  have hzf2w1 : ∀ (e₀ : Fin (mAnnuli p)), jWidth (ssValue Γ e₀) = 1 → ∀ l : Fin r, 1 ≤ (l : ℕ) →
      hasseExp Φ.toFamData l = 2 → ∀ Q ∈ (Δ.annIn e₀).dom, Q.ord (goodFamily Φ' l) = 0 := by
    intro e₀ hw₀ l hl hn2

    intro Q hQ
    by_contra hQord

    obtain ⟨μ, hμ, -, hμA⟩ := ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime hp A hA
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
    set t := goodFamily Φ' with ht
    set c₁ : AlgebraicClosure ℚ := (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l with hc₁
    have hc₁0 : c₁ ≠ 0 := pow_ne_zero _ hp0
    have hc₁A : c₁ ∈ A := pow_mem hpA _
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e₀
    set zo := (Δ.annOut e₀).param with hzo
    have hmod0' : ((Δ.annOut e₀).modulus : AlgebraicClosure ℚ) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : (Δ.annIn e₀).param * zo = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((Δ.annOut e₀).modulus : AlgebraicClosure ℚ) := by
      rw [show (Δ.annIn e₀).param * zo = zo * (Δ.annIn e₀).param from mul_comm _ _, hzo, htwo, hmod]
    have hwide := annOut_wide' p A hA Γ Δ e₀ μ hμA
    have hordt : (nodeTgt Γ e₀).ord ((infChart Γ).residue ⟨t l, hintI' l⟩) = 2 := hItwo e₀ l hl hn2 hw₀
    have hrest : (infChart Γ).residue ⟨t l, hintI' l⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hordt; exact two_ne_zero hordt.symm
    have hscaled : goodFamilyZero Φ'.toFamData l
        = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l := rfl
    have hC't : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c₁)⁻¹ * t l ∈ (zeroChart Γ).integers := by
      rw [← hscaled]; exact hint' l
    have e2 : (⟨_, hC't⟩ : (zeroChart Γ).integers) = ⟨_, hint' l⟩ := Subtype.ext hscaled.symm
    have hβ : (nodeSrc Γ e₀).ord ((zeroChart Γ).residue ⟨_, hC't⟩) = -2 := by
      rw [e2, hatt0, hn2, hw₀]; norm_num
    have hres't : (zeroChart Γ).residue ⟨_, hC't⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hβ; norm_num at hβ
    have hrow : ∀ Y ∈ (Δ.annIn e₀).dom, t l ∈ Y.toValuationSubring :=
      fun Y hY => (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ' μ hμA e₀ Y hY l hl).1
    have hpole : ∀ Y ∈ (Δ.annOut e₀).dom, 0 ≤ Y.ord (t l) := fun Y hY => Y.ord_nonneg_of_mem (hrow Y (hdom ▸ hY))
    obtain ⟨D, hD0, hDsupp, hDord, hdeg, -⟩ :=
      AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
        (Δ.annOut e₀) (Δ.annIn e₀) hdom.symm hmod.symm hmod0' htwo' (infChart Γ) (nodeTgt Γ e₀) (Δ.attached_tgt e₀)
        (zeroChart Γ) (nodeSrc Γ e₀) (Δ.attached_src e₀) hwide (t l) (hintI' l) hrest c₁ hc₁0 hc₁A hC't hres't hpole
    rw [hordt, hβ] at hdeg
    have hDQ : D Q ≠ 0 := by rw [hDord Q (hdom ▸ hQ)]; exact hQord
    have hpos : 0 < D Q := lt_of_le_of_ne (hD0 Q) (Ne.symm hDQ)
    have hle : D Q ≤ D.sum fun _ m => m := by
      rw [Finsupp.sum]
      exact Finset.single_le_sum (fun Y' _ => hD0 Y') (Finsupp.mem_support_iff.2 hDQ)
    omega

  have hzfgen : ∀ (e₀ : Fin (mAnnuli p)) (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = jWidth (ssValue Γ e₀) →
      (nodeTgt Γ e₀).ord ((infChart Γ).residue ⟨goodFamily Φ' l, hintI' l⟩) = 1 →
      ∀ Q ∈ (Δ.annIn e₀).dom, Q.ord (goodFamily Φ' l) = 0 := by
    intro e₀ l hl hn hord
    obtain ⟨μ₀, -, -, hμA₀⟩ := ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime hp A hA
    exact (ModularCurve.MultCovering.forall_ord_goodFamily_eq_zero_and_ord_residue_goodFamilyZero_eq_neg_one_of_hasseExp_eq_jWidth
      p A hA Γ Δ Φ' e₀ l ((hexp l).trans hn) (hintI' l) hord μ₀ hμA₀).1

  have core : ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ (e₁ e₂ : Fin (mAnnuli p)), e₁ ≠ e₂ →
      (jWidth (ssValue Γ e₂) = 1 ∨ (jWidth (ssValue Γ e₁) = 3 ∧ jWidth (ssValue Γ e₂) = 2)) →
      ∀ R₁ ∈ (Δ.annIn e₁).dom, ∀ R₂ ∈ (Δ.annIn e₂).dom,
        (∃ i' j', evalVec s R₁ i' * evalVec s R₂ j' ≠ evalVec s R₁ j' * evalVec s R₂ i') →
        |prox μ (evalVec s R₁) (evalVec s R₂)| ≤ compConst Φ' s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro μ hμ hμA e₁ e₂ hne12 hcond R₁ hR₁ R₂ hR₂ hnp
    have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
    have hμp1 : μ (p : AlgebraicClosure ℚ) < 1 := by
      obtain ⟨a, haA, hpa⟩ := modulus_dvd' Γ Δ e₁
      have hm1 : μ (((Δ.annIn e₁).modulus : AlgebraicClosure ℚ)) < 1 :=
        abv_lt_one_of_mem_maximalIdeal_D μ hμA (Δ.annIn e₁).modulus_mem
      have h3 : μ (p : AlgebraicClosure ℚ) ^ modulusExp < 1 := by
        rw [← map_pow, hpa, map_mul]
        calc μ ((Δ.annIn e₁).modulus : AlgebraicClosure ℚ) * μ a ≤ μ ((Δ.annIn e₁).modulus : AlgebraicClosure ℚ) * 1 :=
              mul_le_mul_of_nonneg_left ((hμA a).1 haA) (μ.nonneg _)
          _ < 1 := by rw [mul_one]; exact hm1
      by_contra hge; push Not at hge
      exact (not_le.2 h3) (one_le_pow₀ hge)

    have ht0 : ∀ l : Fin r, ¬ 1 ≤ (l : ℕ) → goodFamily Φ' l = 1 := fun l hl => Φ'.t_zero l (by omega)
    obtain ⟨l₁, hl₁, hn₁⟩ := hC1
    have hn₁' : hasseExp Φ'.toFamData l₁ = 1 := (hexp l₁).trans hn₁

    have hzeros_wide : ∀ (e₀ : Fin (mAnnuli p)), jWidth (ssValue Γ e₀) ≠ 1 →
        ∀ (R₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))),
        μ (p : AlgebraicClosure ℚ) < μ (R₀.evalAt (Δ.annOut e₀).param) →
        ∀ l : Fin r, ∀ Q ∈ (Δ.annIn e₀).dom, Q.ord (goodFamily Φ' l) ≠ 0 →
          μ (Q.evalAt (Δ.annOut e₀).param) < μ (R₀.evalAt (Δ.annOut e₀).param) := by
      intro e₀ hw₀ R₀ hR₀ l Q hQ hQord
      by_cases hl : 1 ≤ (l : ℕ)
      · obtain ⟨hzd, -⟩ := zerosDepth_D hA Γ Δ Φ' e₀ l hl (hintI' l) (hint' l) (hzinf e₀) (hIwide e₀ l hl hw₀) (hβle e₀ l) μ hμ hμA
        rw [hzd Q hQ hQord]
        refine lt_of_le_of_lt ?_ hR₀
        rcases hexp12 l hl with h1 | h2
        · rw [hexp, h1, pow_one]
        · rw [hexp, h2]; exact pow_le_of_le_one hμp0.le hμp1.le (by norm_num)
      · exfalso; apply hQord; rw [ht0 l hl, Place.ord_one]

    have habove : ∀ (e₀ : Fin (mAnnuli p)) (R₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))),
        R₀ ∈ (Δ.annIn e₀).dom →
        ¬ (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R₀.evalAt (Δ.annOut e₀).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₁ * m) →
        μ (p : AlgebraicClosure ℚ) < μ (R₀.evalAt (Δ.annOut e₀).param) := by
      intro e₀ R₀ hR₀ hnot
      by_contra hle; push Not at hle
      apply hnot
      refine ⟨R₀.evalAt (Δ.annOut e₀).param * (p : AlgebraicClosure ℚ)⁻¹, (hμA _).2 ?_, ?_⟩
      · rw [map_mul, map_inv₀]; exact (mul_inv_le_iff₀ hμp0).2 (by rw [one_mul (μ _)]; exact hle)
      · rw [hn₁', pow_one]; field_simp
    by_cases hw₁ : jWidth (ssValue Γ e₁) = 1
    ·
      have hw₂ : jWidth (ssValue Γ e₂) = 1 := by
        rcases hcond with h | ⟨h3, -⟩
        · exact h
        · rw [hw₁] at h3; exact absurd h3 (by norm_num)
      exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one p hp5 A hA Γ Δ Φ' s hs e₁ e₂ hne12 hw₁ hw₂
        μ hμ hμA R₁ hR₁ R₂ hR₂ hnp
    rcases hcond with hw₂ | ⟨hw₁3, hw₂2⟩
    ·
      have hlt₁ : hasseExp Φ.toFamData l₁ < jWidth (ssValue Γ e₁) := by
        rw [hn₁]; rcases hw_cases e₁ with h | h | h <;> omega
      have hord₁ := hIwide e₁ l₁ hl₁ hw₁
      have hord₁' := hIone e₂ l₁ hl₁ hn₁
      have hβ₁ := hβeq e₁ l₁ hlt₁
      have hzf₁' := ModularCurve.MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one p A hA Γ Δ Φ' e₂ hw₂
        l₁ hl₁ (hintI' l₁) hord₁'
      by_cases hdeep : ∃ m : AlgebraicClosure ℚ, m ∈ A ∧
          R₁.evalAt (Δ.annOut e₁).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₁ * m
      · exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_deep_of_zeroFree p A hA Γ Δ Φ' s hs e₁ e₂ hne12 l₁ hl₁
          (hintI' l₁) hord₁ hord₁' (hint' l₁) hβ₁ hzf₁' μ hμ hμA R₁ hR₁ R₂ hR₂ hdeep hnp
      · have hR₁up := habove e₁ R₁ hR₁ hdeep
        have houtE₁ := hzeros_wide e₁ hw₁ R₁ hR₁up
        have houtE₂ : ∀ l : Fin r, ∀ Q ∈ (Δ.annIn e₂).dom, Q.ord (goodFamily Φ' l) ≠ 0 →
            μ (Q.evalAt (Δ.annOut e₂).param) < μ (R₂.evalAt (Δ.annOut e₂).param) := by
          intro l Q hQ hQord
          exfalso; apply hQord
          by_cases hl : 1 ≤ (l : ℕ)
          · rcases hexp12 l hl with h1 | h2
            · exact ModularCurve.MultCovering.ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one p A hA Γ Δ Φ' e₂ hw₂
                l hl (hintI' l) (hIone e₂ l hl h1) Q hQ
            · exact hzf2w1 e₂ hw₂ l hl h2 Q hQ
          · rw [ht0 l hl, Place.ord_one]
        exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_outer p hp5 A hA Γ Δ Φ' s hs e₁ e₂ hne12
          μ hμ hμA R₁ hR₁ R₂ hR₂ houtE₁ houtE₂ hnp
    ·
      have hw₂ : jWidth (ssValue Γ e₂) ≠ 1 := by rw [hw₂2]; norm_num
      obtain ⟨l₂, l₃, h23, hl₂, hl₃, hn₂, hn₃⟩ := hC2two e₁ e₂ hne12 hw₁ hw₂
      have hβ₁ := hβeq e₁ l₁ (by rw [hn₁, hw₁3]; norm_num)
      have hβ₁' := hβeq e₂ l₁ (by rw [hn₁, hw₂2]; norm_num)
      have hsep₁ := hSEP2 e₁ e₂ l₁ hne12 hw₁ hw₂ hl₁ hn₁
      have hn12 : hasseExp Φ'.toFamData l₁ < hasseExp Φ'.toFamData l₂ := by rw [hexp, hexp, hn₁, hn₂]; norm_num
      have hn13 : hasseExp Φ'.toFamData l₁ < hasseExp Φ'.toFamData l₃ := by rw [hexp, hexp, hn₁, hn₃]; norm_num
      have hzf₂' := hzfgen e₂ l₂ hl₂ (by rw [hn₂, hw₂2]) (hIwide e₂ l₂ hl₂ hw₂)
      have hzf₃' := hzfgen e₂ l₃ hl₃ (by rw [hn₃, hw₂2]) (hIwide e₂ l₃ hl₃ hw₂)

      have hdet : (nodeTgt Γ e₁).evalAt ((infChart Γ).residue ⟨goodFamily Φ' l₂, hintI' l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e₁).param, hzinf e₁⟩)⁻¹)
            * (nodeTgt Γ e₂).evalAt ((infChart Γ).residue ⟨goodFamily Φ' l₃, hintI' l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e₂).param, hzinf e₂⟩)⁻¹)
          ≠ (nodeTgt Γ e₁).evalAt ((infChart Γ).residue ⟨goodFamily Φ' l₃, hintI' l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e₁).param, hzinf e₁⟩)⁻¹)
            * (nodeTgt Γ e₂).evalAt ((infChart Γ).residue ⟨goodFamily Φ' l₂, hintI' l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e₂).param, hzinf e₂⟩)⁻¹) := by
        obtain ⟨hintI₀, hz₀, hz₀', hdet₀⟩ := ModularCurve.MultCovering.tangentDet_ne_zero_of_hasseExp_two p hp13 A hA Γ Δ Φ' hint' hLI'
          e₁ e₂ hne12 hw₁ hw₂ l₂ l₃ h23 ((hexp l₂).trans hn₂) ((hexp l₃).trans hn₃)
        exact hdet₀
      by_cases hdeep : (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R₁.evalAt (Δ.annOut e₁).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₁ * m) ∨
          (∃ m : AlgebraicClosure ℚ, m ∈ A ∧
            R₂.evalAt (Δ.annOut e₂).param = (p : AlgebraicClosure ℚ) ^ hasseExp Φ'.toFamData l₁ * m)
      · exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_leadingTerms p A hA Γ Δ Φ' s hs e₁ e₂ hne12 l₁ l₂ l₃
          hl₁ hl₂ hl₃ hintI' hint' (hzinf e₁) (hzinf e₂) (hIwide e₁ l₁ hl₁ hw₁) (hIwide e₂ l₁ hl₁ hw₂) hβ₁ hβ₁' hsep₁ h23
          (hIwide e₁ l₂ hl₂ hw₁) (hIwide e₂ l₂ hl₂ hw₂) (hIwide e₁ l₃ hl₃ hw₁) (hIwide e₂ l₃ hl₃ hw₂) (hβle e₁ l₂) (hβle e₁ l₃)
          hn12 hn13 hzf₂' hzf₃' hdet μ hμ hμA R₁ hR₁ R₂ hR₂ hdeep hnp
      · have hR₁up := habove e₁ R₁ hR₁ (fun h => hdeep (Or.inl h))
        have hR₂up := habove e₂ R₂ hR₂ (fun h => hdeep (Or.inr h))
        exact ModularCurve.MultCovering.crossComparison_annIn_annIn_of_outer p hp5 A hA Γ Δ Φ' s hs e₁ e₂ hne12
          μ hμ hμA R₁ hR₁ R₂ hR₂ (hzeros_wide e₁ hw₁ R₁ hR₁up) (hzeros_wide e₂ hw₂ R₂ hR₂up) hnp

  intro μ hμ hμA R hR R' hR' hnonprop
  have hsymm : ∀ {e₁ e₂ : Fin (mAnnuli p)} {R₁ R₂ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))},
      (∃ i' j', evalVec s R₁ i' * evalVec s R₂ j' ≠ evalVec s R₁ j' * evalVec s R₂ i') →
      (∃ i' j', evalVec s R₂ i' * evalVec s R₁ j' ≠ evalVec s R₂ j' * evalVec s R₁ i') := by
    intro e₁ e₂ R₁ R₂ ⟨i', j', hij⟩
    exact ⟨j', i', fun h => hij (by rw [mul_comm (evalVec s R₁ i'), mul_comm (evalVec s R₁ j')]; exact h)⟩
  by_cases hw' : jWidth (ssValue Γ e') = 1
  · exact core μ hμ hμA e e' hne (Or.inl hw') R hR R' hR' hnonprop
  by_cases hw : jWidth (ssValue Γ e) = 1
  · rw [prox_symm_D]
    exact core μ hμ hμA e' e (Ne.symm hne) (Or.inl hw) R' hR' R hR (hsymm (e₁ := e) (e₂ := e') hnonprop)

  have hss_inj : Function.Injective (ssValue Γ) := by
    intro a b hab
    unfold ssValue at hab
    exact (Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm.injective (Subtype.ext hab)
  have hne_ss : ssValue Γ e ≠ ssValue Γ e' := fun h => hne (hss_inj h)
  rcases (hwide_iff e).1 hw with he0 | he1728 <;> rcases (hwide_iff e').1 hw' with he'0 | he'1728
  · exact absurd (he0.trans he'0.symm) hne_ss
  · have h3 : jWidth (ssValue Γ e) = 3 := jWidth_of_eq_zero he0
    have h2 : jWidth (ssValue Γ e') = 2 := jWidth_of_eq_1728 he'1728 (by rw [he'1728]; exact h1728)
    exact core μ hμ hμA e e' hne (Or.inr ⟨h3, h2⟩) R hR R' hR' hnonprop
  · have h3 : jWidth (ssValue Γ e') = 3 := jWidth_of_eq_zero he'0
    have h2 : jWidth (ssValue Γ e) = 2 := jWidth_of_eq_1728 he1728 (by rw [he1728]; exact h1728)
    rw [prox_symm_D]
    exact core μ hμ hμA e' e (Ne.symm hne) (Or.inr ⟨h3, h2⟩) R' hR' R hR (hsymm (e₁ := e) (e₂ := e') hnonprop)
  · exact absurd (he1728.trans he'1728.symm) hne_ss

end S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_orth_of_linearIndependent (solution)
