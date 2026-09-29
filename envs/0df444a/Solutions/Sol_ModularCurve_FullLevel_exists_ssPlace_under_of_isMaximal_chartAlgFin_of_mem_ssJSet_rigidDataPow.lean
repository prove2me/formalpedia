-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ssPlace_under_of_isMaximal_chartAlgFin_of_mem_ssJSet_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/6f63ac08-6e04-5497-b3ac-4815ba4f5cd2

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_AlgebraicCurve_exists_place_isRational_forall_evalAt_eq_of_algHom
import Theorems.Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
import Theorems.Thm_ModularCurve_FullLevel_residue_mem_toValuationSubring_of_cuspRegular_of_isRational
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ssJSet_eq_image_algebraMap_of_isAlgClosed
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_of_linearIndependent
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ssPlace_under_of_isMaximal_chartAlgFin_of_mem_ssJSet_rigidDataPow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.pointAddEquivOfEq_refl ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 16000000

noncomputable section

namespace S3A

theorem nonneg_ord_iff_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E) (f : E) :
    0 ≤ v.ord f ↔ f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  constructor
  · exact Place.mem_toValuationSubring_of_ord_nonneg_alt v hf0
  · intro hf
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
    have hcoe : f = ((u : v.toValuationSubring) : E) * ((π : E) ^ (n : ℤ)) := by
      have h := congrArg (Subtype.val) hu
      push_cast at h
      rw [zpow_natCast]
      exact h
    rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
    exact Int.natCast_nonneg n

section Frame

variable (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
  (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
  (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (ℓ' : ℕ) [Fact ℓ'.Prime]
  (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
  [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
  (j : ↥K) [Fact (j ≠ 0)]

def gbar (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M') : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩

omit A R₀ k₀ ℓ' K j in
theorem gbar_add (g₁ g₂ : LaurentSeries ℚ) (h₁ : g₁ ∈ modularFunctionFieldFull M') (h₂ : g₂ ∈ modularFunctionFieldFull M') :
    gbar M' (g₁ + g₂) (add_mem h₁ h₂) = gbar M' g₁ h₁ + gbar M' g₂ h₂ := Subtype.ext (map_add _ _ _)
omit A R₀ k₀ ℓ' K j in
theorem gbar_mul (g₁ g₂ : LaurentSeries ℚ) (h₁ : g₁ ∈ modularFunctionFieldFull M') (h₂ : g₂ ∈ modularFunctionFieldFull M') :
    gbar M' (g₁ * g₂) (mul_mem h₁ h₂) = gbar M' g₁ h₁ * gbar M' g₂ h₂ := Subtype.ext (map_mul _ _ _)
omit A R₀ k₀ ℓ' K j in
theorem gbar_neg (g : LaurentSeries ℚ) (h : g ∈ modularFunctionFieldFull M') :
    gbar M' (-g) (neg_mem h) = -gbar M' g h := Subtype.ext (map_neg _ _)
omit A R₀ k₀ ℓ' K j in
theorem gbar_zero : gbar M' 0 (zero_mem _) = 0 := Subtype.ext (map_zero _)
omit A R₀ k₀ ℓ' K j in
theorem gbar_one : gbar M' 1 (one_mem _) = 1 := Subtype.ext (map_one _)

def Adm (g : LaurentSeries ℚ) : Prop :=
  ∃ (hg : g ∈ modularFunctionFieldFull M') (hgi : gbar M' g hg ∈ R₀.integers),
    (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((gbar M' jq (modularFunctionField_le_full M' (jq_mem M')) : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((gbar M' g hg : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
    ∃ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ K),
      (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j

def N₀ : Subring (LaurentSeries ℚ) where
  carrier := {g | Adm M' A R₀ k₀ ℓ' K j g}
  mul_mem' := by
    rintro g₁ g₂ ⟨hg₁, hgi₁, hc₁, hK₁, hC₁⟩ ⟨hg₂, hgi₂, hc₂, hK₂, hC₂⟩
    have hg : g₁ * g₂ ∈ modularFunctionFieldFull M' := mul_mem hg₁ hg₂
    have hgi : gbar M' (g₁ * g₂) hg ∈ R₀.integers := by
      rw [gbar_mul M' g₁ g₂ hg₁ hg₂]; exact mul_mem hgi₁ hgi₂
    refine ⟨hg, hgi, ?_, ?_⟩
    · intro P hP
      rw [gbar_mul M' g₁ g₂ hg₁ hg₂, S3A.nonneg_ord_iff_mem]
      push_cast
      exact mul_mem ((S3A.nonneg_ord_iff_mem P _).mp (hc₁ P hP)) ((S3A.nonneg_ord_iff_mem P _).mp (hc₂ P hP))
    · have hK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ (g₁ * g₂)) ∈ K := by
        rw [map_mul, map_mul]; exact mul_mem hK₁ hK₂
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = ⟨_, hK₁⟩ * ⟨_, hK₂⟩ := Subtype.ext (by push_cast; rw [map_mul, map_mul])
      rw [e3]; exact mul_mem hC₁ hC₂
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_, ?_⟩
    · rw [gbar_one]; exact one_mem _
    · intro P _; rw [gbar_one]; push_cast; rw [Place.ord_one]
    · have hK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ 1) ∈ K := by rw [map_one, map_one]; exact one_mem _
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = 1 := Subtype.ext (by push_cast; rw [map_one, map_one])
      rw [e3]; exact one_mem _
  add_mem' := by
    rintro g₁ g₂ ⟨hg₁, hgi₁, hc₁, hK₁, hC₁⟩ ⟨hg₂, hgi₂, hc₂, hK₂, hC₂⟩
    have hg : g₁ + g₂ ∈ modularFunctionFieldFull M' := add_mem hg₁ hg₂
    have hgi : gbar M' (g₁ + g₂) hg ∈ R₀.integers := by
      rw [gbar_add M' g₁ g₂ hg₁ hg₂]; exact add_mem hgi₁ hgi₂
    refine ⟨hg, hgi, ?_, ?_⟩
    · intro P hP
      rw [gbar_add M' g₁ g₂ hg₁ hg₂, S3A.nonneg_ord_iff_mem]
      push_cast
      exact add_mem ((S3A.nonneg_ord_iff_mem P _).mp (hc₁ P hP)) ((S3A.nonneg_ord_iff_mem P _).mp (hc₂ P hP))
    · have hK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ (g₁ + g₂)) ∈ K := by
        rw [map_add, map_add]; exact add_mem hK₁ hK₂
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = ⟨_, hK₁⟩ + ⟨_, hK₂⟩ := Subtype.ext (by push_cast; rw [map_add, map_add])
      rw [e3]; exact add_mem hC₁ hC₂
  zero_mem' := by
    refine ⟨zero_mem _, ?_, ?_, ?_⟩
    · rw [gbar_zero]; exact zero_mem _
    · intro P _; rw [gbar_zero]; push_cast; rw [Place.ord_zero]
    · have hK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ 0) ∈ K := by rw [map_zero, map_zero]; exact zero_mem _
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = 0 := Subtype.ext (by push_cast; rw [map_zero, map_zero])
      rw [e3]; exact zero_mem _
  neg_mem' := by
    rintro g ⟨hg₁, hgi₁, hc₁, hK₁, hC₁⟩
    have hg : -g ∈ modularFunctionFieldFull M' := neg_mem hg₁
    have hgi : gbar M' (-g) hg ∈ R₀.integers := by rw [gbar_neg M' g hg₁]; exact neg_mem hgi₁
    refine ⟨hg, hgi, ?_, ?_⟩
    · intro P hP
      rw [gbar_neg M' g hg₁, S3A.nonneg_ord_iff_mem]
      push_cast
      exact neg_mem ((S3A.nonneg_ord_iff_mem P _).mp (hc₁ P hP))
    · have hK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ (-g)) ∈ K := by rw [map_neg, map_neg]; exact neg_mem hK₁
      refine ⟨hK, ?_⟩
      have e3 : (⟨_, hK⟩ : ↥K) = -⟨_, hK₁⟩ := Subtype.ext (by push_cast; rw [map_neg, map_neg])
      rw [e3]; exact neg_mem hC₁

theorem mem_N₀ (g : LaurentSeries ℚ) : g ∈ N₀ M' A R₀ k₀ ℓ' K j ↔ Adm M' A R₀ k₀ ℓ' K j g := Iff.rfl

def ιR : ↥(N₀ M' A R₀ k₀ ℓ' K j) →+* ↥R₀.integers where
  toFun g := ⟨gbar M' (g : LaurentSeries ℚ) g.2.1, g.2.2.1⟩
  map_one' := Subtype.ext (gbar_one M')
  map_mul' g₁ g₂ := Subtype.ext (gbar_mul M' _ _ g₁.2.1 g₂.2.1)
  map_zero' := Subtype.ext (gbar_zero M')
  map_add' g₁ g₂ := Subtype.ext (gbar_add M' _ _ g₁.2.1 g₂.2.1)

def Ψ : ↥(N₀ M' A R₀ k₀ ℓ' K j) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) where
  toFun g := ⟨⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ (g : LaurentSeries ℚ)), g.2.2.2.2.1⟩, g.2.2.2.2.2⟩
  map_one' := Subtype.ext (Subtype.ext (by push_cast; rw [map_one, map_one]))
  map_mul' g₁ g₂ := Subtype.ext (Subtype.ext (by push_cast; rw [map_mul, map_mul]))
  map_zero' := Subtype.ext (Subtype.ext (by push_cast; rw [map_zero, map_zero]))
  map_add' g₁ g₂ := Subtype.ext (Subtype.ext (by push_cast; rw [map_add, map_add]))

theorem Ψ_apply (g : ↥(N₀ M' A R₀ k₀ ℓ' K j)) :
    Ψ M' A R₀ k₀ ℓ' K j g = ⟨⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ (g : LaurentSeries ℚ)), g.2.2.2.2.1⟩, g.2.2.2.2.2⟩ := rfl

end Frame

def liftA (A : ValuationSubring (AlgebraicClosure ℚ)) (g : LaurentSeries ℚ)
    (h : ∀ m : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff m) ∈ A) : LaurentSeries ↥A where
  coeff m := ⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff m), h m⟩
  isPWO_support' := g.isPWO_support'.mono (by
    intro m hm
    rw [Function.mem_support] at hm ⊢
    intro h0
    apply hm
    exact Subtype.ext (by simp [h0]))

theorem coeff_liftA (A : ValuationSubring (AlgebraicClosure ℚ)) (g : LaurentSeries ℚ)
    (h : ∀ m : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff m) ∈ A) (m : ℤ) :
    (liftA A g h).coeff m = ⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff m), h m⟩ := rfl

theorem coeffMap_subtype_liftA (A : ValuationSubring (AlgebraicClosure ℚ)) (g : LaurentSeries ℚ)
    (h : ∀ m : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff m) ∈ A) :
    coeffMap A.subtype (liftA A g h) = coeffEmb (AlgebraicClosure ℚ) g := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff, coeff_liftA]
  rfl

theorem coeff_sum_C_mul (k : Type) [Field k] {ι : Type} [DecidableEq ι] (s : Finset ι) (c : ι → k)
    (f : ι → LaurentSeries k) (n : ℤ) :
    (∑ i ∈ s, HahnSeries.C (c i) * f i).coeff n = ∑ i ∈ s, c i * (f i).coeff n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, HahnSeries.coeff_add, ih, HahnSeries.C_mul_eq_smul,
        HahnSeries.coeff_smul, smul_eq_mul]

theorem coe_sum_algebraMap_mul (k : Type) [Field k] (F : IntermediateField k (LaurentSeries k))
    {ι : Type} (s : Finset ι) (c : ι → k) (x : ι → ↥F) :
    ((∑ i ∈ s, algebraMap k ↥F (c i) * x i : ↥F) : LaurentSeries k) =
      ∑ i ∈ s, HahnSeries.C (c i) * ((x i : ↥F) : LaurentSeries k) := by
  rw [show ((∑ i ∈ s, algebraMap k ↥F (c i) * x i : ↥F) : LaurentSeries k) =
      ∑ i ∈ s, (((algebraMap k ↥F (c i) * x i) : ↥F) : LaurentSeries k) from
    map_sum (F.val : ↥F →+* LaurentSeries k) _ s]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (((algebraMap k ↥F (c i) * x i) : ↥F) : LaurentSeries k) =
      ((algebraMap k ↥F (c i) : ↥F) : LaurentSeries k) * ((x i : ↥F) : LaurentSeries k) from rfl]
  congr 1
  show algebraMap k (LaurentSeries k) (c i) = HahnSeries.C (c i)
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C]

end S3A

end

namespace S3A

lemma sharp_mem_ssJSet
    (q : ℕ) [Fact q.Prime] (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (A₀ : ValuationSubring ↥k₀)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀)) [Algebra ↥A₀ ↥K] [IsScalarTower ↥A₀ ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]
    (hjK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ K)
    (hjC : (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j) →+* Ω)
    (hφ : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    φ ⟨⟨_, hjK⟩, hjC⟩ ∈ ModularCurve.ssJSet q Ω := by

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData ℓ'

  let u : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j) →+* LaurentSeries ↥k₀ :=
    (K.toSubalgebra.val.toRingHom).comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j).val.toRingHom
  have hu : Function.Injective u := by
    intro a b h
    apply Subtype.ext; apply Subtype.ext; exact h
  have huj : u (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j) = coeffEmb ↥k₀ jq := hj
  have husharp : u (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) = qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) := rfl
  have hℚ : data.Φ.eval₂ evalAtJ (jqN ℓ') = 0 := data.eval_eq_zero
  have hk₀ : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ↥k₀)) (coeffEmb ↥k₀ jq))
      (qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq)) = 0 := by
    have h1 := congrArg (coeffEmb ↥k₀) hℚ
    rw [map_zero, Polynomial.hom_eval₂] at h1
    have h2 : (coeffEmb ↥k₀).comp evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ↥k₀)) (coeffEmb ↥k₀ jq) := by
      apply Polynomial.ringHom_ext
      · intro z; simp [Polynomial.eval₂RingHom]
      · rw [RingHom.comp_apply, evalAtJ_X]; simp [Polynomial.eval₂RingHom]
    have h3 : coeffEmb ↥k₀ (jqN ℓ') = qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) := by
      change coeffMap (algebraMap ℚ ↥k₀) (qExpand ℚ ℓ' jq) = qExpand ↥k₀ ℓ' (coeffMap (algebraMap ℚ ↥k₀) jq)
      exact ModularCurve.coeffMap_qExpand _ _ _
    rwa [h2, h3] at h1
  have hC : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j))
      (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) = 0 := by
    apply hu
    rw [map_zero, Polynomial.hom_eval₂, husharp]
    have h2 : u.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j)) =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ↥k₀)) (coeffEmb ↥k₀ jq) := by
      apply Polynomial.ringHom_ext
      · intro z; simp [Polynomial.eval₂RingHom]
      · rw [RingHom.comp_apply]; simp [Polynomial.eval₂RingHom, huj]
    rw [h2]; exact hk₀
  have hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j)))).IsRoot
      (φ (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j))) := by
    have h1 := congrArg φ hC
    rw [map_zero, Polynomial.hom_eval₂] at h1
    have h2 : φ.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j)) =
        Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₀ (↥K) j)) := by
      apply Polynomial.ringHom_ext
      · intro z; simp [Polynomial.eval₂RingHom]
      · rw [RingHom.comp_apply]; simp [Polynomial.eval₂RingHom]
    rw [h2] at h1
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    exact h1
  exact (ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData q ℓ' hℓ'q data Ω _ _ hroot).mp hφ

end S3A

namespace S3A

theorem isIntegral_jNGeomGen_of_modularPolynomialData
    (K : Type) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N)
    (E : Type) [CommRing E] [Algebra E ↥(modularFunctionFieldC K N)]
    (xE : E) (hx : algebraMap E ↥(modularFunctionFieldC K N) xE = jGeomGen K N) :
    IsIntegral E (jNGeomGen K N) := by
  have h := evalModularPair_jGeomGen_eq_zero K N data
  unfold evalModularPair at h
  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom E) xE), data.monic.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap E ↥(modularFunctionFieldC K N)).comp (Polynomial.eval₂RingHom (Int.castRingHom E) xE) =
      Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldC K N)) (jGeomGen K N) := by
    apply Polynomial.ringHom_ext
    · intro z; simp [Polynomial.eval₂RingHom]
    · rw [RingHom.comp_apply]; simp [Polynomial.eval₂RingHom, hx]
  rw [hcomp]
  exact h

theorem isIntegral_adjoin_jNGeomGen
    (K : Type) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) :=
  isIntegral_jNGeomGen_of_modularPolynomialData K N data _
    ⟨jGeomGen K N, IntermediateField.mem_adjoin_simple_self K (jGeomGen K N)⟩ rfl

theorem isIntegral_algebraAdjoin_jNGeomGen
    (K : Type) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(Algebra.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N))) (jNGeomGen K N) :=
  isIntegral_jNGeomGen_of_modularPolynomialData K N data _
    ⟨jGeomGen K N, Algebra.subset_adjoin (Set.mem_singleton (jGeomGen K N))⟩ rfl

theorem finiteDimensional_adjoin_jGeomGen
    (K : Type) [Field K] (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    FiniteDimensional ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
      ↥(modularFunctionFieldC K N) := by
  have hfin : FiniteDimensional ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
      ↥(IntermediateField.adjoin ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
        ({jNGeomGen K N} : Set ↥(modularFunctionFieldC K N))) :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_adjoin_jNGeomGen K N data)
  have hgen : IntermediateField.adjoin K ({jGeomGen K N, jNGeomGen K N} : Set ↥(modularFunctionFieldC K N)) = ⊤ := by
    apply IntermediateField.lift_injective (modularFunctionFieldC K N)
    refine (IntermediateField.lift_adjoin (F := K) (modularFunctionFieldC K N) _).trans ?_
    refine Eq.trans ?_ (IntermediateField.lift_top (F := K) (modularFunctionFieldC K N)).symm
    rw [Set.image_pair]
    rfl
  have htop : IntermediateField.adjoin ↥(IntermediateField.adjoin K ({jGeomGen K N} : Set ↥(modularFunctionFieldC K N)))
      ({jNGeomGen K N} : Set ↥(modularFunctionFieldC K N)) = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := K), IntermediateField.adjoin_simple_adjoin_simple, hgen]
  rw [htop] at hfin
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end S3A

namespace S3A

theorem exists_ssPlace_of_algHom
    (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (W : Finset (Place K ↥(modularFunctionFieldC K N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N K)
    (S : Subalgebra K ↥(modularFunctionFieldC K N)) (hjS : jGeomGen K N ∈ S)
    (hS : ∀ f ∈ S, ∀ w : Place K ↥(modularFunctionFieldC K N), w.IsRational →
      jGeomGen K N ∈ w.toValuationSubring → f ∈ w.toValuationSubring)
    (χ : ↥S →ₐ[K] K) (hχ : χ ⟨jGeomGen K N, hjS⟩ ∈ ssJSet q K) :
    ∃ s : ↥W, ∀ f : ↥S,
      (f : ↥(modularFunctionFieldC K N)) ∈ (s : Place K ↥(modularFunctionFieldC K N)).toValuationSubring ∧
        (s : Place K ↥(modularFunctionFieldC K N)).evalAt (f : ↥(modularFunctionFieldC K N)) = χ f := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  haveI := finiteDimensional_adjoin_jGeomGen K N data
  have hx : ∀ c : K, jGeomGen K N ≠ algebraMap K ↥(modularFunctionFieldC K N) c :=
    fun c h => jGeomGen_sub_algebraMap_ne_zero K N c (sub_eq_zero.mpr h)
  obtain ⟨r, hrat, hxr, hr⟩ :=
    AlgebraicCurve.exists_place_isRational_forall_evalAt_eq_of_algHom K ↥(modularFunctionFieldC K N)
      (jGeomGen K N) hx S hjS hS χ
  have hyr : jNGeomGen K N ∈ r.toValuationSubring := by
    have hint : IsIntegral ↥r.toValuationSubring (jNGeomGen K N) :=
      isIntegral_jNGeomGen_of_modularPolynomialData K N data ↥r.toValuationSubring ⟨jGeomGen K N, hxr⟩ rfl
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥r.toValuationSubring)
      (K := ↥(modularFunctionFieldC K N))).mp hint
    rw [← hz]
    exact z.2
  have hss : r ∈ ssPlaces q N K := by
    refine ⟨hrat, ⟨hxr, hyr⟩, ?_⟩
    rw [(hr ⟨jGeomGen K N, hjS⟩).2]
    exact hχ
  exact ⟨⟨r, (hW r).mpr hss⟩, hr⟩

end S3A

namespace S3A

theorem exists_algHom_range_of_ker_le (K : Type) [Field K] (N B : Type) [CommRing N] [Field B] [Algebra K B]
    (ψ : N →+* B) (φ : N →+* K)
    (hkey : ∀ T : Finset (K × N), (∑ p ∈ T, algebraMap K B p.1 * ψ p.2) = 0 → (∑ p ∈ T, p.1 * φ p.2) = 0) :
    ∃ (S : Subalgebra K B) (χ : ↥S →ₐ[K] K), (∀ n, ψ n ∈ S) ∧ (∀ (n : N) (h : ψ n ∈ S), χ ⟨ψ n, h⟩ = φ n) ∧
      (∀ f ∈ S, ∃ T : Finset (K × N), f = ∑ p ∈ T, algebraMap K B p.1 * ψ p.2) := by
  classical
  let θB : MonoidAlgebra K N →ₐ[K] B := MonoidAlgebra.lift K B N ψ.toMonoidHom
  let θK : MonoidAlgebra K N →ₐ[K] K := MonoidAlgebra.lift K K N φ.toMonoidHom

  let T : MonoidAlgebra K N → Finset (K × N) := fun x => x.coeff.support.image fun n => (x.coeff n, n)
  have hTinj : ∀ x : MonoidAlgebra K N, Set.InjOn (fun n => (x.coeff n, n)) ↑x.coeff.support :=
    fun x a _ b _ h => congrArg Prod.snd h
  have hθB : ∀ x, θB x = ∑ p ∈ T x, algebraMap K B p.1 * ψ p.2 := by
    intro x
    rw [Finset.sum_image (hTinj x)]
    rfl
  have hθK : ∀ x, θK x = ∑ p ∈ T x, p.1 * φ p.2 := by
    intro x
    rw [Finset.sum_image (hTinj x)]
    rfl
  have hker : RingHom.ker θB.rangeRestrict.toRingHom ≤ RingHom.ker θK.toRingHom := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hx' : θB x = 0 := by
      have := congrArg Subtype.val hx
      simpa using this
    change θK x = 0
    rw [hθK]
    exact hkey _ (by rw [← hθB]; exact hx')
  let χ : ↥θB.range →ₐ[K] K :=
    AlgHom.liftOfSurjective θB.rangeRestrict (AlgHom.rangeRestrict_surjective θB) θK hker
  refine ⟨θB.range, χ, ?_, ?_, ?_⟩
  · intro n
    exact ⟨MonoidAlgebra.of K N n, MonoidAlgebra.lift_of _ _⟩
  · intro n h
    have h1 : (⟨ψ n, h⟩ : ↥θB.range) = θB.rangeRestrict (MonoidAlgebra.of K N n) := by
      apply Subtype.ext
      change ψ n = θB (MonoidAlgebra.of K N n)
      exact (MonoidAlgebra.lift_of _ _).symm
    rw [h1]
    show AlgHom.liftOfSurjective θB.rangeRestrict (AlgHom.rangeRestrict_surjective θB) θK hker
      (θB.rangeRestrict (MonoidAlgebra.of K N n)) = φ n
    rw [AlgHom.liftOfSurjective_apply]
    exact MonoidAlgebra.lift_of _ _
  · rintro f ⟨x, rfl⟩
    exact ⟨T x, hθB x⟩

end S3A

noncomputable section
namespace S3A

theorem coeffMap_smul {k κ : Type} [CommRing k] [CommRing κ] (e : k →+* κ) (r : k) (x : LaurentSeries k) :
    ModularCurve.coeffMap e (r • x) = e r • ModularCurve.coeffMap e x := by
  ext m
  simp [ModularCurve.coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul]

theorem sum_mul_eq_zero_of_sum_algebraMap_mul_eq_zero
    (κ : Type) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (B : Type) [Field B] [Algebra κ B] (ι : B →+* LaurentSeries κ) (hι : Function.Injective ι)
    (hιalg : ∀ c : κ, ι (algebraMap κ B c) = HahnSeries.C c)
    (N : Type) [AddCommGroup N] (ψ : N →+ B) (φ : N →+ κ)
    (hrat : ∀ (n : N) (m : ℤ), (ι (ψ n)).coeff m ∈ (⊥ : Subfield κ))
    (h0 : ∀ n : N, ψ n = 0 → φ n = 0) :
    ∀ T : Finset (κ × N), (∑ x ∈ T, algebraMap κ B x.1 * ψ x.2) = 0 → (∑ x ∈ T, x.1 * φ x.2) = 0 := by
  classical
  intro T hT
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let e : ↥(⊥ : Subfield κ) →+* κ := (⊥ : Subfield κ).subtype
  let g : ZeroHom κ ↥(⊥ : Subfield κ) :=
    { toFun := fun c => if h : c ∈ (⊥ : Subfield κ) then ⟨c, h⟩ else 0
      map_zero' := by simp only [dif_pos (⊥ : Subfield κ).zero_mem]; rfl }
  have hg : ∀ c : κ, c ∈ (⊥ : Subfield κ) → e (g c) = c := by
    intro c hc
    have h1 : g c = ⟨c, hc⟩ := by
      show (if h : c ∈ (⊥ : Subfield κ) then (⟨c, h⟩ : ↥(⊥ : Subfield κ)) else 0) = ⟨c, hc⟩
      rw [dif_pos hc]
    rw [h1]
    rfl
  have hnat : ∀ r : ↥(⊥ : Subfield κ), ∃ z : ℕ, (z : κ) = e r := by
    intro r
    have hr : (r : κ) ∈ (ZMod.castHom (dvd_refl p) κ).fieldRange :=
      (bot_le : (⊥ : Subfield κ) ≤ (ZMod.castHom (dvd_refl p) κ).fieldRange) r.2
    obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp hr
    refine ⟨y.val, ?_⟩
    show ((y.val : ℕ) : κ) = (r : κ)
    rw [← hy, ZMod.castHom_apply, ZMod.cast_eq_val]

  let s : ↥T → LaurentSeries ↥(⊥ : Subfield κ) := fun i => (ι (ψ i.1.2)).map g
  have hs : ∀ i : ↥T, ModularCurve.coeffMap e (s i) = ι (ψ i.1.2) := by
    intro i
    ext m
    show e (g ((ι (ψ i.1.2)).coeff m)) = (ι (ψ i.1.2)).coeff m
    exact hg _ (hrat _ m)

  obtain ⟨J, a, ha, hspan, hli⟩ := exists_linearIndependent' (↥(⊥ : Subfield κ)) s
  haveI : Fintype J := Fintype.ofInjective a ha
  have hmem : ∀ i : ↥T, s i ∈ Submodule.span ↥(⊥ : Subfield κ) (Set.range (s ∘ a)) := by
    intro i
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose r hr using fun i : ↥T => (Submodule.mem_span_range_iff_exists_fun ↥(⊥ : Subfield κ)).mp (hmem i)
  choose z hz using fun (i : ↥T) (j : J) => hnat (r i j)

  have hψ : ∀ i : ↥T, ψ i.1.2 = ∑ j, (z i j : ℕ) • ψ (a j).1.2 := by
    intro i
    apply hι
    rw [← hs i, ← hr i, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.comp_apply, coeffMap_smul, hs (a j), map_nsmul, ← Nat.cast_smul_eq_nsmul κ (z i j), hz i j]
  have hφ : ∀ i : ↥T, φ i.1.2 = ∑ j, (z i j : κ) * φ (a j).1.2 := by
    intro i
    have h1 : ψ (i.1.2 - ∑ j, (z i j : ℕ) • (a j).1.2) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero, hψ i]
      exact Finset.sum_congr rfl fun j _ => (map_nsmul ψ _ _).symm
    have h2 := h0 _ h1
    rw [map_sub, map_sum, sub_eq_zero] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun j _ => by rw [map_nsmul, nsmul_eq_mul]

  have hli' := ModularCurve.linearIndependent_coeffMap_of_linearIndependent (↥(⊥ : Subfield κ)) κ e J (s ∘ a) hli
  have h1 : ∑ i : ↥T, i.1.1 • ι (ψ i.1.2) = 0 := by
    calc ∑ i : ↥T, i.1.1 • ι (ψ i.1.2) = ∑ x ∈ T, x.1 • ι (ψ x.2) :=
          Finset.sum_coe_sort T (fun x => x.1 • ι (ψ x.2))
      _ = ∑ x ∈ T, ι (algebraMap κ B x.1 * ψ x.2) :=
          Finset.sum_congr rfl fun x _ => by rw [map_mul, hιalg, HahnSeries.C_mul_eq_smul]
      _ = ι (∑ x ∈ T, algebraMap κ B x.1 * ψ x.2) := (map_sum ι _ T).symm
      _ = 0 := by rw [hT, map_zero]
  have hrelκ : ∑ j, (∑ i : ↥T, i.1.1 * (z i j : κ)) • ModularCurve.coeffMap e ((s ∘ a) j) = 0 := by
    refine Eq.trans ?_ h1
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψ i, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.comp_apply, hs (a j), map_nsmul, ← Nat.cast_smul_eq_nsmul κ (z i j), smul_smul]
  have hcoef : ∀ j, ∑ i : ↥T, i.1.1 * (z i j : κ) = 0 := fun j =>
    Fintype.linearIndependent_iff.mp hli' _ hrelκ j

  calc ∑ x ∈ T, x.1 * φ x.2 = ∑ i : ↥T, i.1.1 * φ i.1.2 := (Finset.sum_coe_sort T (fun x => x.1 * φ x.2)).symm
    _ = ∑ i : ↥T, ∑ j, (i.1.1 * (z i j : κ)) * φ (a j).1.2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφ i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, (∑ i : ↥T, i.1.1 * (z i j : κ)) * φ (a j).1.2 := by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = 0 := Finset.sum_eq_zero fun j _ => by rw [hcoef j, zero_mul]

theorem mem_bot_of_mul_den_eq_num (κ : Type) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (r : κ) (x : ℚ) (h : r * (x.den : κ) = (x.num : κ)) : r ∈ (⊥ : Subfield κ) := by
  by_cases hd : (x.den : κ) = 0
  · exfalso
    have hnum : ((x.num : ℤ) : κ) = 0 := by rw [← h, hd, mul_zero]
    have h1 : p ∣ x.den := (CharP.cast_eq_zero_iff κ p x.den).mp hd
    have h2 : (p : ℤ) ∣ x.num := (CharP.intCast_eq_zero_iff κ p x.num).mp hnum
    have h3 : p ∣ x.num.natAbs := Int.natCast_dvd.mp h2
    have h4 : p ∣ Nat.gcd x.num.natAbs x.den := Nat.dvd_gcd h3 h1
    rw [x.reduced] at h4
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h4)
  · have hr : r = (x.num : κ) / (x.den : κ) := by rw [eq_div_iff hd, h]
    rw [hr]
    exact div_mem (intCast_mem _ x.num) (natCast_mem _ x.den)

end S3A

end

theorem S3A.qExpand_mem_of_residue_eq_zero
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ℓ' : ℕ) [Fact ℓ'.Prime]
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (hcusp : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M')))
    (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ K)
    (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)
    (hres0 : R₀.residue ⟨_, hgi⟩ = 0)
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hmy : ∀ r : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), r ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) r ∈ y) :
    (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) ∈ y := by
  classical
  have hqp : q.Prime := Fact.out
  have hq0 : ((q : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero
  have hq0' : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero

  have hq𝔪A : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact_mod_cast hA

  have hunitZ : ∀ m : ℤ, ¬ (q : ℤ) ∣ m → IsUnit ((m : ℤ) : ↥A) := by
    intro m hm
    by_contra hu
    have hm𝔪 : ((m : ℤ) : ↥A) ∈ maximalIdeal ↥A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hu
    have hm' : ¬ q ∣ m.natAbs := fun h => hm (Int.natCast_dvd.mpr h)
    have hcop : IsCoprime (m : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hm')
    obtain ⟨a, b, hab⟩ := hcop
    have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
      have : ((a : ℤ) : ↥A) * (m : ℤ) + ((b : ℤ) : ↥A) * ((q : ℕ) : ↥A) = 1 := by
        have := congrArg (Int.cast : ℤ → ↥A) hab
        push_cast at this
        exact this
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm𝔪) (Ideal.mul_mem_left _ _ hq𝔪A)
    exact (maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

  have hcoeffEmbC : ∀ (F : Type) [Field F] [Algebra ℚ F] (c : ℚ),
      coeffEmb F (HahnSeries.C c) = HahnSeries.C (algebraMap ℚ F c) := by
    intro F _ _ c
    rw [HahnSeries.C_apply, HahnSeries.C_apply]
    exact coeffMap_single _ _ _

  have hlift : ∀ (f : LaurentSeries ℚ), (∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (f.coeff n) ∈ A) →
      ∃ yA : LaurentSeries ↥A, coeffMap A.subtype yA = coeffEmb (AlgebraicClosure ℚ) f := by
    intro f hf
    refine ⟨⟨fun n => ⟨algebraMap ℚ (AlgebraicClosure ℚ) (f.coeff n), hf n⟩, ?_⟩, ?_⟩
    · have : (Function.support fun n => (⟨algebraMap ℚ (AlgebraicClosure ℚ) (f.coeff n), hf n⟩ : ↥A)) = Function.support f.coeff := by
        ext n
        simp only [Function.mem_support, ne_eq]
        rw [← ZeroMemClass.coe_eq_zero]
        show ¬ algebraMap ℚ (AlgebraicClosure ℚ) (f.coeff n) = 0 ↔ ¬ f.coeff n = 0
        rw [map_eq_zero_iff _ (algebraMap ℚ (AlgebraicClosure ℚ)).injective]
      rw [this]
      exact f.isPWO_support'
    · ext n
      rw [coeffMap_coeff, coeffEmb_coeff]
      rfl

  have hcoefA := ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀ g hg hgi hcusp
  obtain ⟨yA, hyA⟩ := hlift g hcoefA
  have hy : coeffMap A.subtype yA ∈ modularFunctionFieldBar M' := by
    rw [hyA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg
  obtain ⟨hint, hres⟩ := hR₀ yA hy
  have helt : (⟨⟨coeffMap A.subtype yA, hy⟩, hint⟩ : ↥R₀.integers) =
      ⟨⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩, hgi⟩ := by
    apply Subtype.ext; apply Subtype.ext; exact hyA
  have hres' : coeffMap (IsLocalRing.residue ↥A) yA = 0 := by
    rw [← hres, helt, hres0]; rfl
  have hyAn : ∀ n : ℤ, ((yA.coeff n : ↥A) : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n) := by
    intro n
    have : (coeffMap A.subtype yA).coeff n = (coeffEmb (AlgebraicClosure ℚ) g).coeff n := by rw [hyA]
    rw [coeffMap_coeff, coeffEmb_coeff] at this
    exact this
  have hcoef𝔪 : ∀ n : ℤ, (⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n), hcoefA n⟩ : ↥A) ∈ maximalIdeal ↥A := by
    intro n
    have h := congrArg (fun x : LaurentSeries (ResidueField ↥A) => x.coeff n) hres'
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h
    have : yA.coeff n = ⟨algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n), hcoefA n⟩ := Subtype.ext (hyAn n)
    rw [← this]
    exact (IsLocalRing.residue_eq_zero_iff _).mp h

  have hdiv : ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g.coeff n / q) ∈ A := by
    intro n
    set r : ℚ := g.coeff n with hr
    have hrA : algebraMap ℚ (AlgebraicClosure ℚ) r ∈ A := hcoefA n
    have hrm : (⟨algebraMap ℚ (AlgebraicClosure ℚ) r, hrA⟩ : ↥A) ∈ maximalIdeal ↥A := hcoef𝔪 n
    have hden0 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz

    have hnum : (q : ℤ) ∣ r.num := by
      by_contra hnd
      have hu := hunitZ r.num hnd
      have hmul : ((r.num : ℤ) : ↥A) = (⟨algebraMap ℚ (AlgebraicClosure ℚ) r, hrA⟩ : ↥A) * ((r.den : ℕ) : ↥A) := by
        apply Subtype.ext
        show ((r.num : ℤ) : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) r * ((r.den : ℕ) : AlgebraicClosure ℚ)
        rw [eq_ratCast, Rat.cast_def, div_mul_cancel₀ _ (by exact_mod_cast hden0)]
      have : ((r.num : ℤ) : ↥A) ∈ maximalIdeal ↥A := by rw [hmul]; exact Ideal.mul_mem_right _ _ hrm
      exact ((IsLocalRing.mem_maximalIdeal _).mp this) hu
    obtain ⟨k, hk⟩ := hnum

    have hden : ¬ (q : ℤ) ∣ (r.den : ℤ) := by
      intro hd
      have h1 : q ∣ r.num.natAbs := Int.natCast_dvd.mp ⟨k, hk⟩
      have h2 : q ∣ r.den := Int.natCast_dvd_natCast.mp hd
      have hc : Nat.Coprime q r.den := Nat.Coprime.coprime_dvd_left h1 r.reduced
      exact hqp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h2)
    obtain ⟨v, hv⟩ := (hunitZ r.den hden).exists_right_inv
    have hvQ : (((r.den : ℕ) : ℤ) : AlgebraicClosure ℚ) * ((v : ↥A) : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun x : ↥A => (x : AlgebraicClosure ℚ)) hv
      exact this
    have hdeninv : ((r.den : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      have : ((v : ↥A) : AlgebraicClosure ℚ) = ((r.den : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
        rw [Int.cast_natCast] at hvQ
        exact (eq_inv_of_mul_eq_one_right hvQ)
      rw [← this]; exact v.2
    have hrq : r / q = (k : ℚ) / r.den := by
      conv_lhs => rw [← Rat.num_div_den r, hk]
      push_cast
      field_simp
    rw [hrq, map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
    exact mul_mem (intCast_mem A k) hdeninv

  set g₁ : LaurentSeries ℚ := HahnSeries.C ((q : ℚ)⁻¹) * g with hg₁def
  have hg₁coeff : ∀ n : ℤ, g₁.coeff n = g.coeff n / q := by
    intro n
    rw [hg₁def, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, div_eq_inv_mul]
  have hCalg : ∀ (F : Type) [Field F] (c : F), HahnSeries.C c = algebraMap F (LaurentSeries F) c := by
    intro F _ c
    rw [ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl
  have hg₁ : g₁ ∈ modularFunctionFieldFull M' := by
    rw [hg₁def]
    refine mul_mem ?_ hg
    rw [hCalg]
    exact IntermediateField.algebraMap_mem _ _
  have hcoefA₁ : ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (g₁.coeff n) ∈ A := fun n => by rw [hg₁coeff]; exact hdiv n
  obtain ⟨yA₁, hyA₁⟩ := hlift g₁ hcoefA₁
  have hy₁ : coeffMap A.subtype yA₁ ∈ modularFunctionFieldBar M' := by
    rw [hyA₁]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg₁
  obtain ⟨hint₁, -⟩ := hR₀ yA₁ hy₁
  have hgi₁ : (⟨coeffEmb (AlgebraicClosure ℚ) g₁, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg₁⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by
    have helt₁ : (⟨coeffMap A.subtype yA₁, hy₁⟩ : ↥(modularFunctionFieldBar M')) =
        ⟨coeffEmb (AlgebraicClosure ℚ) g₁, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg₁⟩ := Subtype.ext hyA₁
    rw [← helt₁]; exact hint₁
  have hcoeffEmb₁ : coeffEmb (AlgebraicClosure ℚ) g₁ = HahnSeries.C (((q : ℕ) : AlgebraicClosure ℚ)⁻¹) * coeffEmb (AlgebraicClosure ℚ) g := by
    rw [hg₁def, map_mul, hcoeffEmbC, map_inv₀, map_natCast]
  have hcusp₁ : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g₁, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg₁⟩ : ↥(modularFunctionFieldBar M')) :
        ↥(modularFunctionFieldBar M')) := by
    intro P hP
    have helt₁ : (⟨coeffEmb (AlgebraicClosure ℚ) g₁, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg₁⟩ : ↥(modularFunctionFieldBar M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (((q : ℕ) : AlgebraicClosure ℚ)⁻¹) *
          (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) := by
      apply Subtype.ext
      show coeffEmb (AlgebraicClosure ℚ) g₁ = ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (((q : ℕ) : AlgebraicClosure ℚ)⁻¹) : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) * coeffEmb (AlgebraicClosure ℚ) g
      rw [hcoeffEmb₁, hCalg]
      rfl
    rw [helt₁, ← Algebra.smul_def, ConstantReduction.ord_smul P (inv_ne_zero hq0')]
    exact hcusp P hP
  have hgK₁ : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g₁) ∈ K := by
    have : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g₁) =
        HahnSeries.C (algebraMap ℚ ↥k₀ ((q : ℚ)⁻¹)) * ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) := by
      rw [hg₁def, map_mul, map_mul, hcoeffEmbC, ModularCurve.qExpand_C]
    rw [this]
    refine mul_mem ?_ hgK
    rw [hCalg]
    exact IntermediateField.algebraMap_mem _ _
  have mem₁ := ModularCurve.FullLevel.qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
    q M' hqM' A hA R₀ hR₀ k₀ ℓ' K hK j hj g₁ hg₁ hgi₁ hcusp₁ hgK₁

  have hq𝔪 : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hvQ : ((q : ℕ) : AlgebraicClosure ℚ) * (((v : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun x : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => ((x : ↥k₀) : AlgebraicClosure ℚ)) hv
      push_cast at this
      exact this
    have hinv : ((q : ℕ) : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      rw [← eq_inv_of_mul_eq_one_right hvQ]; exact v.2
    rcases (ValuationSubring.mem_nonunits_iff_or A).mp hA with h | h
    · exact hq0' h
    · exact h hinv
  have key : (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) * ⟨⟨_, hgK₁⟩, mem₁⟩ := by
    apply Subtype.ext; apply Subtype.ext
    show ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) =
      (((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) : ↥K) : LaurentSeries ↥k₀) * ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g₁)
    rw [map_natCast, hg₁def, map_mul, map_mul, hcoeffEmbC, ModularCurve.qExpand_C, ← mul_assoc]
    have : ((((q : ℕ) : ↥K)) : LaurentSeries ↥k₀) * HahnSeries.C (algebraMap ℚ ↥k₀ ((q : ℚ)⁻¹)) = 1 := by
      rw [map_inv₀, map_natCast, show (((q : ℕ) : ↥K) : LaurentSeries ↥k₀) = HahnSeries.C ((q : ℕ) : ↥k₀) by
        rw [map_natCast]; norm_cast, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hqp.ne_zero), map_one]
    rw [this, one_mul]
  rw [key]
  exact Ideal.mul_mem_right _ _ (hmy _ hq𝔪)

set_option maxHeartbeats 160000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (hjK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ K)
    (hjC : (⟨_, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :
    ∀ (y' : {y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) // y.IsMaximal ∧ algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y}),
      (∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* Ω),
        RingHom.ker φ = y'.1 →
          φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ∈ ModularCurve.ssJSet q Ω) →
      ∃ s : ↥W,
        (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
              ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ K)
            (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
          ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
            (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩ ∈ y'.1) := by
  intro y' hss'
  classical

  have hqp : q.Prime := Fact.out
  haveI hκac : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI hymax : (y'.1).IsMaximal := y'.2.1
  have hπy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨π₀, hπ⟩ ∈ y'.1 := y'.2.2
  haveI : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := hres

  let incl : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ↥A :=
    { toFun := fun x => ⟨((x : ↥k₀) : AlgebraicClosure ℚ), x.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  haveI hloc : IsLocalHom incl := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hx
    have hb' : ((x : ↥k₀) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hb
      first | simpa using this | exact this | (simp at this; exact this)
    have hx0 : ((x : ↥k₀) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; rw [h, zero_mul] at hb'; exact zero_ne_one hb'
    have hbeq : (b : AlgebraicClosure ℚ) = ((x : ↥k₀) : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
    have hbk : ((x : ↥k₀)⁻¹ : ↥k₀) ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) := by
      rw [ValuationSubring.mem_comap]
      change (((x : ↥k₀)⁻¹ : ↥k₀) : AlgebraicClosure ℚ) ∈ A
      push_cast
      rw [← hbeq]; exact b.2
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : ↥k₀)⁻¹, hbk⟩, ?_⟩
    apply Subtype.ext
    change (x : ↥k₀) * (x : ↥k₀)⁻¹ = 1
    exact mul_inv_cancel₀ (fun h => hx0 (by rw [h]; simp))
  let e : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* ResidueField ↥A := IsLocalRing.ResidueField.map incl
  have he : ∀ (c : ↥k₀) (hc : (c : AlgebraicClosure ℚ) ∈ A),
      e (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨c, hc⟩) = residue ↥A ⟨(c : AlgebraicClosure ℚ), hc⟩ := fun c hc => rfl

  have hkill : ∀ x ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ((Ideal.Quotient.mk y'.1).comp (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))) x = 0 := by
    intro x hx
    rw [hunif, Ideal.mem_span_singleton] at hx
    obtain ⟨d, rfl⟩ := hx
    rw [RingHom.comp_apply, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hπy, zero_mul]
  let ι₀ : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⧸ y'.1) := Ideal.Quotient.lift _ _ hkill
  have hι₀ : ∀ x : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ι₀ (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) x) = Ideal.Quotient.mk y'.1 (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) x) := fun x => rfl
  haveI : Nontrivial (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⧸ y'.1) := Ideal.Quotient.nontrivial_iff.mpr hymax.ne_top

  have hmy : ∀ r ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) r ∈ y'.1 := by
    intro r hr
    rw [hunif, Ideal.mem_span_singleton] at hr
    obtain ⟨d, rfl⟩ := hr
    rw [map_mul]; exact Ideal.mul_mem_right _ _ hπy
  have hbij : Function.Bijective ι₀ := by
    refine ⟨ι₀.injective, fun z => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨c, hc⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin hres (j : ↥K) y'.1 hymax hmy b
    refine ⟨residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) c, ?_⟩
    rw [hι₀, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hc

  let eqv : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ≃+* (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⧸ y'.1) := RingEquiv.ofBijective ι₀ hbij
  have heqv : ∀ z, eqv z = ι₀ z := fun z => rfl
  let valHom : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := eqv.symm.toRingHom.comp (Ideal.Quotient.mk y'.1)
  have hval : ∀ c, ι₀ (valHom c) = Ideal.Quotient.mk y'.1 c := by
    intro c
    rw [← heqv]
    exact eqv.apply_symm_apply _
  have hinj : ∀ a b : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ι₀ a = ι₀ b → a = b := fun a b hab => hbij.1 hab
  have hval_alg : ∀ x : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), valHom (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) x) = residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) x := by
    intro x
    exact hinj _ _ ((hval (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) x)).trans (hι₀ x).symm)
  have hker : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), valHom c = 0 ↔ c ∈ y'.1 := by
    intro c
    have h1 := hval c
    constructor
    · intro h
      have h3 : Ideal.Quotient.mk y'.1 c = 0 := h1.symm.trans ((congrArg ι₀ h).trans ι₀.map_zero)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h3
    · intro h
      have h2 : Ideal.Quotient.mk y'.1 c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
      exact hinj _ _ (h1.trans (h2.trans ι₀.map_zero.symm))

  let Ψ := S3A.Ψ M' A R₀ k₀ ℓ' K j
  let ιR := S3A.ιR M' A R₀ k₀ ℓ' K j
  let ψ : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j) →+* ↥(modularFunctionFieldC (ResidueField ↥A) M') := R₀.residue.comp ιR
  let φ : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j) →+* ResidueField ↥A := e.comp (valHom.comp Ψ)
  have hφ : ∀ g, φ g = e (valHom (Ψ g)) := fun g => rfl
  have hΨ : ∀ g : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j), (((Ψ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) : LaurentSeries ↥k₀) =
      ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ (g : LaurentSeries ℚ)) := fun g => rfl

  have hcoefA : ∀ (g : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j)) (m : ℤ),
      algebraMap ℚ (AlgebraicClosure ℚ) ((g : LaurentSeries ℚ).coeff m) ∈ A := fun g m =>
    ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀ (g : LaurentSeries ℚ)
      g.2.1 g.2.2.1 g.2.2.2.1 m

  have hψcoeff : ∀ (g : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j)) (m : ℤ),
      ((ψ g : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff m
        = residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((g : LaurentSeries ℚ).coeff m), hcoefA g m⟩ := by
    intro g m
    have hy : coeffMap A.subtype (S3A.liftA A (g : LaurentSeries ℚ) (hcoefA g)) ∈ modularFunctionFieldBar M' := by
      rw [S3A.coeffMap_subtype_liftA]; exact (S3A.gbar M' _ g.2.1).2
    obtain ⟨hint, hres⟩ := hR₀ (S3A.liftA A (g : LaurentSeries ℚ) (hcoefA g)) hy
    have e1 : (⟨⟨coeffMap A.subtype (S3A.liftA A _ (hcoefA g)), hy⟩, hint⟩ : ↥R₀.integers) = ιR g :=
      Subtype.ext (Subtype.ext (S3A.coeffMap_subtype_liftA A _ (hcoefA g)))
    show (((R₀.residue (ιR g)) : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff m = _
    rw [← e1, hres, coeffMap_coeff, S3A.coeff_liftA]
  haveI hκch : CharP (ResidueField ↥A) q := by
    have hq' : ((q : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
    have hmem : (q : ↥A) ∈ maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
    have h0 : ((q : ℕ) : ResidueField ↥A) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]; exact hmem
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0

  have hφ0 : ∀ n : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j), ψ n = 0 → φ n = 0 := by
    intro n hn
    have hres0 : R₀.residue ⟨_, n.2.2.1⟩ = 0 := hn
    have hmem : Ψ n ∈ y'.1 :=
      S3A.qExpand_mem_of_residue_eq_zero q M' hqM' A hA R₀ hR₀ k₀ ℓ' K hK j hj (n : LaurentSeries ℚ)
        n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2.1 n.2.2.2.2.2 hres0 y'.1 hmy
    rw [hφ, (hker _).mpr hmem, map_zero]
  let ιF : ↥(modularFunctionFieldC (ResidueField ↥A) M') →+* LaurentSeries (ResidueField ↥A) := (modularFunctionFieldC (ResidueField ↥A) M').val.toRingHom
  have hιF : ∀ f, ιF f = ((f : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) := fun _ => rfl
  have hιFinj : Function.Injective ιF := fun a b h => Subtype.ext h
  have hιFalg : ∀ c : (ResidueField ↥A), ιF (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c) = HahnSeries.C c := by
    intro c
    rw [hιF]
    show algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) c = HahnSeries.C c
    rw [ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl
  have hrat : ∀ (n : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j)) (m : ℤ), (ιF (ψ.toAddMonoidHom n)).coeff m ∈ (⊥ : Subfield (ResidueField ↥A)) := by
    intro n m
    rw [hιF]
    show ((ψ n : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)).coeff m ∈ (⊥ : Subfield (ResidueField ↥A))
    rw [hψcoeff]
    apply S3A.mem_bot_of_mul_den_eq_num (ResidueField ↥A) q _ ((n : LaurentSeries ℚ).coeff m)
    have hA1 : (⟨algebraMap ℚ (AlgebraicClosure ℚ) ((n : LaurentSeries ℚ).coeff m), hcoefA n m⟩ : ↥A)
        * ((((n : LaurentSeries ℚ).coeff m).den : ℕ) : ↥A) = ((((n : LaurentSeries ℚ).coeff m).num : ℤ) : ↥A) := by
      apply Subtype.ext
      push_cast
      rw [← map_natCast (algebraMap ℚ (AlgebraicClosure ℚ)), ← map_mul, Rat.mul_den_eq_num, map_intCast]
    have := congrArg (residue ↥A) hA1
    rwa [map_mul, map_natCast, map_intCast] at this
  have KEY : ∀ T : Finset (ResidueField ↥A × ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j)),
      (∑ p ∈ T, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') p.1 * ψ p.2) = 0 → (∑ p ∈ T, p.1 * φ p.2) = 0 :=
    fun T hT => S3A.sum_mul_eq_zero_of_sum_algebraMap_mul_eq_zero (ResidueField ↥A) q ↥(modularFunctionFieldC (ResidueField ↥A) M') ιF hιFinj hιFalg
      ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j) ψ.toAddMonoidHom φ.toAddMonoidHom hrat hφ0 T hT

  obtain ⟨S, χ, hψS, hχψ, hSgen⟩ :=
    S3A.exists_algHom_range_of_ker_le (ResidueField ↥A) ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j) ↥(modularFunctionFieldC (ResidueField ↥A) M') ψ φ KEY

  have hmapA : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    change (jqModC ↥A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC, map_jqModC]
  have hjqBar : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hmapA]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjint, hjres⟩ := hR₀ (jqModC ↥A) hjqBar
  have helt : (S3A.gbar M' jq (modularFunctionField_le_full M' (jq_mem M')) : ↥(modularFunctionFieldBar M')) =
      ⟨coeffMap A.subtype (jqModC ↥A), hjqBar⟩ := Subtype.ext hmapA.symm
  have hjgi : S3A.gbar M' jq (modularFunctionField_le_full M' (jq_mem M')) ∈ R₀.integers := by rw [helt]; exact hjint
  have hjAdm : S3A.Adm M' A R₀ k₀ ℓ' K j jq :=
    ⟨modularFunctionField_le_full M' (jq_mem M'), hjgi, fun P h => h, hjK, hjC⟩
  let jN : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j) := ⟨jq, hjAdm⟩
  have hψj : ψ jN = jGeomGen (ResidueField ↥A) M' := by
    show R₀.residue (ιR jN) = _
    have h1 : ιR jN = ⟨_, hjint⟩ := Subtype.ext helt
    rw [h1]
    apply Subtype.ext
    rw [hjres, coe_jGeomGen]
    change (jqModC ↥A).map (IsLocalRing.residue ↥A) = jqModC (ResidueField ↥A)
    exact map_jqModC _
  have hjS : jGeomGen (ResidueField ↥A) M' ∈ S := by rw [← hψj]; exact hψS jN
  have hΨj : Ψ jN = (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) := rfl

  have hkerφ' : RingHom.ker (e.comp valHom) = y'.1 := by
    ext c
    rw [RingHom.mem_ker, RingHom.comp_apply, ← hker c]
    constructor
    · intro h; exact e.injective (h.trans e.map_zero.symm)
    · intro h; rw [h, map_zero]
  have hjss : e (valHom (⟨⟨_, hjK⟩, hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))) ∈ ssJSet q (ResidueField ↥A) := by
    have h1 := hss' (ResidueField ↥A) (e.comp valHom) hkerφ'
    exact S3A.sharp_mem_ssJSet q ℓ' hℓ'q k₀ (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) K j hj hjK hjC
      (ResidueField ↥A) (e.comp valHom) h1
  have hχj : χ ⟨jGeomGen (ResidueField ↥A) M', hjS⟩ ∈ ssJSet q (ResidueField ↥A) := by
    have h2 : χ ⟨jGeomGen (ResidueField ↥A) M', hjS⟩ = φ jN := by
      have := hχψ jN (hψS jN)
      rw [← this]
      congr 1
      exact Subtype.ext hψj.symm
    rw [h2, hφ, hΨj]
    exact hjss

  have hSreg : ∀ f ∈ S, ∀ w : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'), w.IsRational →
      jGeomGen (ResidueField ↥A) M' ∈ w.toValuationSubring → f ∈ w.toValuationSubring := by
    intro f hf w hw hjw
    obtain ⟨T, rfl⟩ := hSgen f hf
    refine Subring.sum_mem _ (fun p _ => Subring.mul_mem _ (w.algebraMap_mem' p.1) ?_)
    exact ModularCurve.FullLevel.residue_mem_toValuationSubring_of_cuspRegular_of_isRational q M' hqM' A hA R₀ hR₀
      (p.2 : LaurentSeries ℚ) p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 w hw hjw
  obtain ⟨s, hs⟩ := S3A.exists_ssPlace_of_algHom q (ResidueField ↥A) M' hqM' W hW S hjS hSreg χ hχj

  refine ⟨s, ?_⟩
  intro g hg hgi hcusp hreg hgK hgC c hc hcval
  let gN : ↥(S3A.N₀ M' A R₀ k₀ ℓ' K j) := ⟨g, hg, hgi, hcusp, hgK, hgC⟩
  have hψg : ψ gN = R₀.residue ⟨_, hgi⟩ := rfl
  obtain ⟨-, hev⟩ := hs ⟨ψ gN, hψS gN⟩

  have h1 : e (valHom (Ψ gN)) = residue ↥A ⟨(c : AlgebraicClosure ℚ), hc⟩ := by
    rw [hcval, ← hψg, ← hφ, ← hχψ gN (hψS gN)]
    exact hev.symm
  have h2 : valHom (Ψ gN) = valHom (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩) := by
    apply e.injective
    rw [h1, hval_alg, he]
  have h3 : valHom (Ψ gN - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ⟨c, hc⟩) = 0 := by rw [map_sub, h2, sub_self]
  exact (hker _).mp h3

end S_ModularCurve_FullLevel_exists_ssPlace_under_of_isMaximal_chartAlgFin_of_mem_ssJSet_rigidDataPow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ssPlace_under_of_isMaximal_chartAlgFin_of_mem_ssJSet_rigidDataPow (solution)
