-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/428748a1-01a4-5684-9afa-b7e2c29f4728

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_ModularCurve_MultCovering_abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_zeroChart
import Theorems.Thm_ModularCurve_MultCovering_crossComparison_annIn_annIn
import Theorems.Thm_ModularCurve_MultCovering_infChart_chartData_goodFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁"
p2m_attr_erase "instance" "instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.LevelOnePhi.instAddCommGroup ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of"
p2m_attr_erase "simp" "AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar MultCovering.abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom MultCovering.abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom MultCovering.one_le_hasseExp MultCovering.crossComparison_annIn_zeroChart MultCovering.crossComparison_annIn_annIn"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "nCharts mAnnuli ChartCtx infChart zeroChart chart chart_zero chart_one AnnCtx hasseExp FamCtx goodFamily compConst abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom one_le_hasseExp crossComparison_annIn_zeroChart crossComparison_annIn_annIn infChart_chartData_goodFamily"
p2m_open "ModularCurve.MultCovering ModularCurve"

open AlgebraicCurve IsLocalRing

theorem prox_comm' {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {r : ℕ} (x y : Fin r → K) :
    prox μ x y = prox μ y x := by
  simp only [prox]
  have : (⨆ q : Fin r × Fin r, μ (x q.1 * y q.2 - x q.2 * y q.1))
      = ⨆ q : Fin r × Fin r, μ (y q.1 * x q.2 - y q.2 * x q.1) :=
    (Equiv.prodComm (Fin r) (Fin r)).iSup_congr fun q => by
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      congr 1; ring
  rw [this]; ring

theorem prox_comm_abs {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {r : ℕ} (x y : Fin r → K) :
    |prox μ x y| = |prox μ y x| := by rw [prox_comm']

theorem nonprop_symm' {r : ℕ} {x y : Fin r → AlgebraicClosure ℚ}
    (h : ∃ i' j', x i' * y j' ≠ x j' * y i') : ∃ i' j', y i' * x j' ≠ y j' * x i' := by
  obtain ⟨i, j, hij⟩ := h
  exact ⟨i, j, fun h' => hij (by rw [mul_comm (x i), mul_comm (x j)]; exact h'.symm)⟩

set_option maxHeartbeats 1600000 in
theorem crossComparison_infChart_of_forall_small (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ (infChart Γ).dom, ∀ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
        Q.IsRational →
        (∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ Q.toValuationSubring ∧ μ (Q.evalAt (goodFamily Φ l)) < 1) →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA P hP Q hQrat hsmall hnp
  obtain ⟨hint, cQ, iQ, hrat, hcQ, hratio, hreg, himm, hsep, hhasse⟩ :=
    infChart_chartData_goodFamily p hp5 A hA Γ Φ
  exact ModularCurve.MultCovering.abs_prox_evalVec_le_of_mem_infChart_dom_of_forall_abv_evalAt_goodFamily_lt_one
    p hp5 Φ s hs A hA Γ μ hμ hμA hint cQ (fun P hP => (hrat P hP).1) hratio hreg (hhasse μ hμA) P hP Q hQrat hsmall hnp

theorem crossComparison_infChart_annIn (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ (infChart Γ).dom, ∀ e : Fin (mAnnuli p), ∀ Q ∈ (Δ.annIn e).dom,
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA P hP e Q hQ hnp
  have hQrat : Q.IsRational := ((Δ.annIn e).mem_dom Q hQ).1
  exact crossComparison_infChart_of_forall_small p hp5 Φ s hs A hA Γ Δ μ hμ hμA P hP Q hQrat
    (fun l hl => ModularCurve.MultCovering.abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e Q hQ l hl) hnp

theorem crossComparison_infChart_zeroChart (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ (infChart Γ).dom, ∀ Q ∈ (zeroChart Γ).dom,
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA P hP Q hQ hnp
  obtain ⟨hQrat, hC1⟩ := ModularCurve.MultCovering.abv_evalAt_goodFamily_le_pow_hasseExp_of_mem_zeroChart_dom p A hA Γ Φ μ hμA Q hQ
  have hp : p.Prime := Fact.out
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hμp1 : μ (p : AlgebraicClosure ℚ) < 1 := by
    have hmax : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(p : AlgebraicClosure ℚ), hpA⟩)).1 hA
    have hle : μ (p : AlgebraicClosure ℚ) ≤ 1 := (hμA _).1 hpA
    refine lt_of_le_of_ne hle fun h1 => ?_
    apply (IsLocalRing.mem_maximalIdeal _).1 hmax
    have hinv : (p : AlgebraicClosure ℚ)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
    exact isUnit_iff_exists_inv.2 ⟨⟨(p : AlgebraicClosure ℚ)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hp0)⟩
  refine crossComparison_infChart_of_forall_small p hp5 Φ s hs A hA Γ Δ μ hμ hμA P hP Q hQrat (fun l hl => ⟨(hC1 l).1, ?_⟩) hnp
  have hn : 1 ≤ hasseExp Φ.toFamData l := ModularCurve.MultCovering.one_le_hasseExp p A hA Γ Φ l hl
  exact lt_of_le_of_lt (hC1 l).2 (pow_lt_one₀ (μ.nonneg _) hμp1 (by omega))

end ModularCurve.MultCovering

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom.ModularCurve.MultCovering"

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → modularFunctionFieldBar (1 * p)) (hs : IsEmbBasis (1 * p) s)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hpart : ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), (∃ i, P ∈ (chart Γ i).dom) ∨ (∃ e, P ∈ (Δ.annIn e).dom)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
    (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
    ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      (∀ i, P ∈ (chart Γ i).dom → Q ∉ (chart Γ i).dom) →
      (∀ e, P ∈ (Δ.annIn e).dom → Q ∉ (Δ.annIn e).dom) →
      (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  intro μ hμ hμA P Q hchart htube hnp
  have hc0 : ∀ X : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), X ∈ (chart Γ 0).dom ↔ X ∈ (infChart Γ).dom := by
    intro X; rw [chart_zero]
  have hc1 : ∀ X : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), X ∈ (chart Γ 1).dom ↔ X ∈ (zeroChart Γ).dom := by
    intro X; rw [chart_one]
  have key : ∀ (X Y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (i : Fin nCharts),
      X ∈ (chart Γ i).dom → Y ∉ (chart Γ i).dom →
      ((∃ j, Y ∈ (chart Γ j).dom) ∨ (∃ e, Y ∈ (Δ.annIn e).dom)) →
      (∃ i' j', evalVec s X i' * evalVec s Y j' ≠ evalVec s X j' * evalVec s Y i') →
      |prox μ (evalVec s X) (evalVec s Y)| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro X Y i hX hY hYpart hnpXY
    rcases hYpart with ⟨j, hYj⟩ | ⟨e, hYe⟩
    · have hij : i ≠ j := fun h => hY (h ▸ hYj)
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact ModularCurve.MultCovering.crossComparison_infChart_zeroChart p hp5 Φ s hs A hA Γ Δ μ hμ hμA X ((hc0 X).1 hX) Y ((hc1 Y).1 hYj) hnpXY
      · rw [ModularCurve.MultCovering.prox_comm_abs]
        exact ModularCurve.MultCovering.crossComparison_infChart_zeroChart p hp5 Φ s hs A hA Γ Δ μ hμ hμA Y ((hc0 Y).1 hYj) X ((hc1 X).1 hX)
          (ModularCurve.MultCovering.nonprop_symm' hnpXY)
      · exact absurd rfl hij
    · fin_cases i
      · exact ModularCurve.MultCovering.crossComparison_infChart_annIn p hp5 Φ s hs A hA Γ Δ μ hμ hμA X ((hc0 X).1 hX) e Y hYe hnpXY
      · rw [ModularCurve.MultCovering.prox_comm_abs]
        exact ModularCurve.MultCovering.crossComparison_annIn_zeroChart p hp5 Φ s hs A hA Γ Δ μ hμ hμA e Y hYe X ((hc1 X).1 hX) (ModularCurve.MultCovering.nonprop_symm' hnpXY)
  rcases hpart P with ⟨i, hPi⟩ | ⟨e, hPe⟩
  · exact key P Q i hPi (hchart i hPi) (hpart Q) hnp
  · rcases hpart Q with ⟨j, hQj⟩ | ⟨e', hQe'⟩
    · have hPj : P ∉ (chart Γ j).dom := fun h => hchart j h hQj
      rw [ModularCurve.MultCovering.prox_comm_abs]
      exact key Q P j hQj hPj (Or.inr ⟨e, hPe⟩) (ModularCurve.MultCovering.nonprop_symm' hnp)
    · have hne : e ≠ e' := fun h => htube e hPe (h ▸ hQe')
      exact ModularCurve.MultCovering.crossComparison_annIn_annIn p hp5 Φ s hs A hA Γ Δ e e' hne μ hμ hμA P hPe Q hQe' hnp

end S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_of_forall_mem_chart_dom_or_mem_annIn_dom (solution)
