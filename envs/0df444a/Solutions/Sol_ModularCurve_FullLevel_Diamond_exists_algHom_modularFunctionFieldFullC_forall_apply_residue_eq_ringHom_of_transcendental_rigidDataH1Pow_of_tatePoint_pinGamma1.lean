-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_algHom_modularFunctionFieldFullC_forall_apply_residue_eq_ringHom_of_transcendental_rigidDataH1Pow_of_tatePoint_pinGamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5ca10839-0c13-50cc-949f-e9f37aca4376

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
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_ModularCurve_ModuliPointMap
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_swapBivar_eq_of_evalSymm
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_ModularCurve_FullLevel_exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible_of_prime
import Theorems.Thm_ModularCurve_FullLevel_Diamond_coeffEmb_mem_chartAlgFin_of_cuspRegular_of_mem_integers
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_ModularCurve_FullLevel_exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
import Theorems.Thm_ModularCurve_FullLevel_mem_integers_and_cuspRegular_qExpand_jq_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_qExpand_coeffEmb_mem_chartAlgFin_of_mem_integers_of_cuspRegular_of_not_dvd
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_algHom_modularFunctionFieldFullC_forall_apply_residue_eq_ringHom_of_transcendental_rigidDataH1Pow_of_tatePoint_pinGamma1
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply"
p2m_attr_erase "simp" "AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 32000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
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

    (P₀ : LevelModuliPackageAbs ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx₀ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries ↥k₀) = ModularCurve.jqNModC ↥k₀ q)
    (clC : P₀.B₀ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hclC : ∀ b : P₀.B₀, ((clC b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = P₀.classify x₀ b)
    (hμ : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ∃ (C : WeierstrassCurve.VariableChange (LaurentSeries ↥k₀)) (r : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).Raw ↥K),
      (Quot.mk _ r : (WeierstrassCurve.DrinfeldGlobal.rigidDataH1Pow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K) = x₀ ∧

      (((C.u : (LaurentSeries ↥k₀)ˣ) : LaurentSeries ↥k₀) * (2 * (ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : ↥k₀)⁻¹)) =
          2 * (ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C.r = HahnSeries.C (-(12 : ↥k₀)⁻¹) ∧ C.s = HahnSeries.C (-(2 : ↥k₀)⁻¹) ∧ C.t = HahnSeries.C ((24 : ↥k₀)⁻¹)) ∧

      r.curve.map (algebraMap ↥K (LaurentSeries ↥k₀)) = C • ModularCurve.tateBase ↥k₀ q ∧

      (∀ (p : ↥M'.primeFactors) (F' : Type) [Field F'] (f : ↥k₀ →+* F') (ζ : F'),
        IsPrimitiveRoot ζ ((p : ℕ) ^ M'.factorization (p : ℕ)) →
        ((r.level.1 p).map (algebraMap ↥K (LaurentSeries ↥k₀))).map (ModularCurve.coeffMap f) =
          ModularCurve.kernelVariableChangeDeg (C.map (ModularCurve.coeffMap f))
            (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
            (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
              (Polynomial.X - Polynomial.C (ModularCurve.toricPoint F' q (ζ ^ a)).1))) ∧

      r.level.2.1.map (algebraMap ↥K (LaurentSeries ↥k₀)) =
        (⟨(ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2, (ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries ↥k₀)).variableChange C ∧

      (∃ Px Py Qx Qy : ↥K,
        (Px : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xP ∧
        (Py : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yP ∧
        (Qx : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).xQ ∧
        (Qy : LaurentSeries ↥k₀) = ((ModularCurve.cuspData ↥k₀ q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(1 : ZMod q), 0] ![0, -(1 : ZMod q)]).variableChange C).yQ ∧
        IsSectionThrough r.level.2.2.P Px Py ∧ IsSectionThrough r.level.2.2.Q Qx Qy))
    (θ : (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →+* (ResidueField ↥A))
    (hθ : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), θ (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a) =
      IsLocalRing.residue ↥A ⟨((a : ↥k₀) : AlgebraicClosure ℚ), ValuationSubring.mem_comap.mp a.2⟩)  :
    ∀ (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) (_ : y.IsMaximal)
        (ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), ψ c = 0 ↔ c ∈ y),
        ∀
        (Ω : Type) [Field Ω] [DecidableEq Ω] [Algebra (ResidueField ↥A) Ω]
        (V : Place (ResidueField ↥A) Ω)
        (res : ResidueField ↥V.toValuationSubring →+* (ResidueField ↥A))
        (ρ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →+* ↥V.toValuationSubring)
        (hr : ∀ c : (ResidueField ↥A), res (algebraMap (ResidueField ↥A) (ResidueField ↥V.toValuationSubring) c) = c)
        (hs : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
          ((ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) a) : ↥V.toValuationSubring) : Ω) =
            algebraMap (ResidueField ↥A) Ω (θ (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a)))
        (hp : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), res (IsLocalRing.residue ↥V.toValuationSubring (ρ c)) = θ (ψ c))
        (ht : Transcendental (ResidueField ↥A) ((ρ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) : ↥V.toValuationSubring) : Ω)),
      ∃ emb : ↥(ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M') →ₐ[(ResidueField ↥A)] Ω,
        (∀ (gf : LaurentSeries ℚ) (hgf : gf ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) :
              ↥(modularFunctionFieldBar M'))) →
          ∀ (hgK : (coeffEmb ↥k₀ gf) ∈ K)
            (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
            emb (IntermediateField.inclusion (ModularCurve.modularFunctionFieldC_le_full (ResidueField ↥A) M') (R₀.residue ⟨_, hgi⟩)) =
              ((ρ ⟨⟨_, hgK⟩, hgC⟩ : ↥V.toValuationSubring) : Ω)) ∧
        (∀ (d : ℕ) [NeZero d] (hd : d ∣ M')
            (hgK : (coeffEmb ↥k₀ (ModularCurve.qExpand ℚ d ModularCurve.jq)) ∈ K)
            (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
            emb (ModularCurve.jqNFull (ResidueField ↥A) M' d hd) = ((ρ ⟨⟨_, hgK⟩, hgC⟩ : ↥V.toValuationSubring) : Ω)) := by
  intro y hy ψ hψ Ω _ _ _ V res ρ hr hs hp ht
  classical

  let ebar : LaurentSeries ℚ → ↥(modularFunctionFieldBar M') := fun gf =>
    if hgf : gf ∈ modularFunctionFieldFull M' then (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) else 0
  have ebar_eq : ∀ (gf) (hgf : gf ∈ modularFunctionFieldFull M'), ebar gf = (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) := fun gf hgf => dif_pos hgf

  let Adm : LaurentSeries ℚ → Prop := fun gf =>
    ∃ (hgf : gf ∈ modularFunctionFieldFull M') (_ : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers), (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), 0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')))

  have hFsub : ∀ a b : LaurentSeries ℚ, a ∈ modularFunctionFieldFull M' → b ∈ modularFunctionFieldFull M' →
      a + b ∈ modularFunctionFieldFull M' ∧ a * b ∈ modularFunctionFieldFull M' :=
    fun a b ha hb => ⟨add_mem ha hb, mul_mem ha hb⟩
  have embBar_add : ∀ (a b) (ha : a ∈ modularFunctionFieldFull M') (hb : b ∈ modularFunctionFieldFull M'),
      ((⟨coeffEmb (AlgebraicClosure ℚ) (a + b), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hFsub a b ha hb).1⟩ : ↥(modularFunctionFieldBar M'))) = (⟨coeffEmb (AlgebraicClosure ℚ) a, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ha⟩ : ↥(modularFunctionFieldBar M')) + (⟨coeffEmb (AlgebraicClosure ℚ) b, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hb⟩ : ↥(modularFunctionFieldBar M')) := fun a b ha hb => Subtype.ext (map_add _ a b)
  have embBar_mul : ∀ (a b) (ha : a ∈ modularFunctionFieldFull M') (hb : b ∈ modularFunctionFieldFull M'),
      ((⟨coeffEmb (AlgebraicClosure ℚ) (a * b), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hFsub a b ha hb).2⟩ : ↥(modularFunctionFieldBar M'))) = (⟨coeffEmb (AlgebraicClosure ℚ) a, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ha⟩ : ↥(modularFunctionFieldBar M')) * (⟨coeffEmb (AlgebraicClosure ℚ) b, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hb⟩ : ↥(modularFunctionFieldBar M')) := fun a b ha hb => Subtype.ext (map_mul _ a b)
  have embBar_neg : ∀ (a) (ha : a ∈ modularFunctionFieldFull M'),
      ((⟨coeffEmb (AlgebraicClosure ℚ) (-a), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (neg_mem ha)⟩ : ↥(modularFunctionFieldBar M'))) = -(⟨coeffEmb (AlgebraicClosure ℚ) a, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ha⟩ : ↥(modularFunctionFieldBar M')) := fun a ha => Subtype.ext (map_neg _ a)
  have embBar_zero : ((⟨coeffEmb (AlgebraicClosure ℚ) 0, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (zero_mem _)⟩ : ↥(modularFunctionFieldBar M'))) = 0 := Subtype.ext (map_zero _)
  have embBar_one : ((⟨coeffEmb (AlgebraicClosure ℚ) 1, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (one_mem _)⟩ : ↥(modularFunctionFieldBar M'))) = 1 := Subtype.ext (map_one _)

  have ord_nonneg_add : ∀ (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (f g : ↥(modularFunctionFieldBar M')), 0 ≤ P.ord f → 0 ≤ P.ord g → 0 ≤ P.ord (f + g) := by
    intro P f g hf hg
    by_cases hf0 : f = 0
    · rw [hf0, zero_add]; exact hg
    by_cases hg0 : g = 0
    · rw [hg0, add_zero]; exact hf
    by_cases hfg : f + g = 0
    · rw [hfg, AlgebraicCurve.Place.ord_zero]
    exact le_trans (le_min hf hg) (AlgebraicCurve.Place.min_ord_le_ord_add P hf0 hg0 hfg)
  have ord_nonneg_mul : ∀ (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (f g : ↥(modularFunctionFieldBar M')), 0 ≤ P.ord f → 0 ≤ P.ord g → 0 ≤ P.ord (f * g) := by
    intro P f g hf hg
    by_cases hf0 : f = 0
    · rw [hf0, zero_mul, AlgebraicCurve.Place.ord_zero]
    by_cases hg0 : g = 0
    · rw [hg0, mul_zero, AlgebraicCurve.Place.ord_zero]
    rw [AlgebraicCurve.Place.ord_mul P hf0 hg0]; exact add_nonneg hf hg
  have ord_neg_one : ∀ (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')), P.ord (-1 : ↥(modularFunctionFieldBar M')) = 0 := by
    intro P
    have h := AlgebraicCurve.Place.ord_mul P (neg_ne_zero.mpr (one_ne_zero' ↥(modularFunctionFieldBar M'))) (neg_ne_zero.mpr (one_ne_zero' ↥(modularFunctionFieldBar M')))
    rw [neg_one_mul, neg_neg, AlgebraicCurve.Place.ord_one] at h
    omega
  have ord_nonneg_neg : ∀ (P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (f : ↥(modularFunctionFieldBar M')), 0 ≤ P.ord f → 0 ≤ P.ord (-f) := by
    intro P f hf
    by_cases hf0 : f = 0
    · rw [hf0, neg_zero, AlgebraicCurve.Place.ord_zero]
    rw [← neg_one_mul, AlgebraicCurve.Place.ord_mul P (neg_ne_zero.mpr (one_ne_zero' ↥(modularFunctionFieldBar M'))) hf0, ord_neg_one, zero_add]
    exact hf

  let 𝒜 : Subring (LaurentSeries ℚ) :=
    { carrier := {gf | Adm gf}
      mul_mem' := by
        rintro a b ⟨ha, hai, hac⟩ ⟨hb, hbi, hbc⟩
        refine ⟨mul_mem ha hb, ?_, ?_⟩
        · rw [embBar_mul a b ha hb]; exact mul_mem hai hbi
        · intro P hP; rw [embBar_mul a b ha hb]; exact ord_nonneg_mul P _ _ (hac P hP) (hbc P hP)
      one_mem' := ⟨one_mem _, by rw [embBar_one]; exact one_mem _, fun P hP => by
        rw [embBar_one, AlgebraicCurve.Place.ord_one]⟩
      add_mem' := by
        rintro a b ⟨ha, hai, hac⟩ ⟨hb, hbi, hbc⟩
        refine ⟨add_mem ha hb, ?_, ?_⟩
        · rw [embBar_add a b ha hb]; exact add_mem hai hbi
        · intro P hP; rw [embBar_add a b ha hb]; exact ord_nonneg_add P _ _ (hac P hP) (hbc P hP)
      zero_mem' := ⟨zero_mem _, by rw [embBar_zero]; exact zero_mem _, fun P hP => by
        rw [embBar_zero, AlgebraicCurve.Place.ord_zero]⟩
      neg_mem' := by
        rintro a ⟨ha, hai, hac⟩
        refine ⟨neg_mem ha, ?_, ?_⟩
        · rw [embBar_neg a ha]; exact neg_mem hai
        · intro P hP; rw [embBar_neg a ha]; exact ord_nonneg_neg P _ (hac P hP) }
  have h𝒜 : ∀ gf : LaurentSeries ℚ, gf ∈ 𝒜 ↔ Adm gf := fun gf => Iff.rfl

  have hK_of : ∀ (gf : LaurentSeries ℚ), gf ∈ modularFunctionFieldFull M' →
      coeffEmb ↥k₀ gf ∈ K := by
    intro gf hgf
    rw [hK]
    have h1 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
      ↥k₀ M' 1 (q ^ 2 * M') ⟨q ^ 2, by ring⟩ H₁ gf hgf
    rwa [ModularCurve.qExpand_one_apply] at h1
  have hC_of : ∀ (gf : LaurentSeries ℚ) (hgf : gf ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) (hcusp : (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), 0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))))
      (hgK : coeffEmb ↥k₀ gf ∈ K),
      (⟨_, hgK⟩ : ↥K) ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := by
    intro gf hgf hgi hcusp hgK
    exact ModularCurve.FullLevel.Diamond.coeffEmb_mem_chartAlgFin_of_cuspRegular_of_mem_integers q M' hqM' ℓg hℓg hℓg12 hℓgM'
      A hA W hW hle R₀ hR₀ s k₀ π₀ hπ hdvr hunif hhens hres hκ ξ hξ hιξ H₁ hH₁ K hK j hj gf hgf hgi hcusp hgK

  let sharp : ↥𝒜 → ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) := fun gf =>
    ⟨⟨_, hK_of gf.1 gf.2.1⟩, hC_of gf.1 gf.2.1 gf.2.2.1 gf.2.2.2 (hK_of gf.1 gf.2.1)⟩
  have sharp_coe : ∀ gf : ↥𝒜, (((sharp gf : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) : LaurentSeries ↥k₀) =
      coeffEmb ↥k₀ (gf : LaurentSeries ℚ) := fun _ => rfl
  have sharp_add : ∀ a b : ↥𝒜, sharp (a + b) = sharp a + sharp b := fun a b => by
    apply Subtype.ext; apply Subtype.ext
    show coeffEmb ↥k₀ ((a : LaurentSeries ℚ) + b) = _
    rw [map_add]; rfl
  have sharp_mul : ∀ a b : ↥𝒜, sharp (a * b) = sharp a * sharp b := fun a b => by
    apply Subtype.ext; apply Subtype.ext
    show coeffEmb ↥k₀ ((a : LaurentSeries ℚ) * b) = _
    rw [map_mul]; rfl
  have sharp_one : sharp 1 = 1 := by
    apply Subtype.ext; apply Subtype.ext
    show coeffEmb ↥k₀ (1 : LaurentSeries ℚ) = _
    rw [map_one]; rfl
  have sharp_zero : sharp 0 = 0 := by
    apply Subtype.ext; apply Subtype.ext
    show coeffEmb ↥k₀ (0 : LaurentSeries ℚ) = _
    rw [map_zero]; rfl

  let val : ↥𝒜 →+* Ω :=
    { toFun := fun gf => ((ρ (sharp gf) : ↥V.toValuationSubring) : Ω)
      map_one' := by show ((ρ (sharp 1) : ↥V.toValuationSubring) : Ω) = 1; rw [sharp_one, map_one]; rfl
      map_mul' := fun a b => by
        show ((ρ (sharp (a * b)) : ↥V.toValuationSubring) : Ω) = ((ρ (sharp a) : ↥V.toValuationSubring) : Ω) * ((ρ (sharp b) : ↥V.toValuationSubring) : Ω)
        rw [sharp_mul, map_mul]; rfl
      map_zero' := by show ((ρ (sharp 0) : ↥V.toValuationSubring) : Ω) = 0; rw [sharp_zero, map_zero]; rfl
      map_add' := fun a b => by
        show ((ρ (sharp (a + b)) : ↥V.toValuationSubring) : Ω) = ((ρ (sharp a) : ↥V.toValuationSubring) : Ω) + ((ρ (sharp b) : ↥V.toValuationSubring) : Ω)
        rw [sharp_add, map_add]; rfl }
  have val_apply : ∀ gf : ↥𝒜, val gf = ((ρ (sharp gf) : ↥V.toValuationSubring) : Ω) := fun _ => rfl

  haveI : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  have hq0 : (((ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))) : ↥V.toValuationSubring) : Ω) = 0 := by
    rw [hs, map_natCast, map_natCast, CharP.cast_eq_zero, map_zero]
  have hnat : ((q : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) _ ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := (map_natCast _ q).symm
  have hval0 : ∀ (gf : LaurentSeries ℚ) (h : gf ∈ 𝒜) (hgf : gf ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField ↥A) M') = 0 → val ⟨gf, h⟩ = 0 := by
    intro gf h hgf hgi hres0
    obtain ⟨_, hgi0, hcusp⟩ := h
    obtain ⟨gf', hgf', heq, hgi', hcusp'⟩ :=
      ModularCurve.FullLevel.exists_eq_smul_of_residue_eq_zero_of_mem_integers_of_cuspRegular q M' hqM' A hA R₀ hR₀ gf hgf hgi hcusp hres0
    have h' : gf' ∈ 𝒜 := ⟨hgf', hgi', hcusp'⟩
    have e1 : coeffEmb ↥k₀ gf =
        ((q : ℕ) : LaurentSeries ↥k₀) * coeffEmb ↥k₀ gf' := by
      rw [heq, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, map_mul, map_natCast]
    have helt : sharp ⟨gf, ⟨hgf, hgi0, hcusp⟩⟩ = ((q : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) * sharp ⟨gf', h'⟩ := by
      apply Subtype.ext; apply Subtype.ext
      refine (sharp_coe _).trans (e1.trans ?_)
      push_cast
      rfl
    rw [val_apply, helt, hnat, map_mul, Subring.coe_mul, hq0, zero_mul]

  have hj𝒜 : jq ∈ 𝒜 := by
    refine ⟨modularFunctionField_le_full M' (jq_mem M'), ?_, fun P h => h⟩
    have hid1 : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
      show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
      exact coeffMap_jqModC _
    have hy1 : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [coeffMap_jqModC, ← hid1]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
    obtain ⟨h1, -⟩ := hR₀ (jqModC ↥A) hy1
    have heq1 : (⟨coeffMap A.subtype (jqModC ↥A), hy1⟩ : ↥(modularFunctionFieldBar M')) =
        ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :=
      Subtype.ext (show coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq by rw [coeffMap_jqModC, hid1])
    exact heq1 ▸ h1
  have hvalj : Transcendental (ResidueField ↥A) (val ⟨jq, hj𝒜⟩) := by

    have hsh : sharp ⟨jq, hj𝒜⟩ = AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by
      apply Subtype.ext; apply Subtype.ext
      rw [sharp_coe]
      show coeffEmb ↥k₀ jq = ((j : ↥K) : LaurentSeries ↥k₀)
      exact hj.symm
    rw [val_apply, hsh]; exact ht

  obtain ⟨emb, hemb⟩ := ModularCurve.FullLevel.exists_algHom_modularFunctionFieldFullC_of_ringHom_admissible_of_prime q M' hqM' A hA R₀ hR₀ 𝒜 h𝒜 hj𝒜 Ω val hval0 hvalj
  refine ⟨emb, ?_, ?_⟩
  ·
    intro gf hgf hgi hcusp hgK hgC
    rw [hemb gf ⟨hgf, hgi, hcusp⟩ hgf hgi, val_apply]
  ·
    intro d _ hd hgK hgC
    obtain ⟨hgi, hcusp⟩ := ModularCurve.FullLevel.mem_integers_and_cuspRegular_qExpand_jq_of_dvd M' A R₀ hR₀ d hd
    have hgf : ModularCurve.qExpand ℚ d ModularCurve.jq ∈ modularFunctionFieldFull M' := ModularCurve.jqd_mem_full M' hd
    have hfloor : IntermediateField.inclusion (ModularCurve.modularFunctionFieldC_le_full (ResidueField ↥A) M')
        (R₀.residue ⟨_, hgi⟩) = ModularCurve.jqNFull (ResidueField ↥A) M' d hd := by
      have hid : coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d jq) = jqNModC (AlgebraicClosure ℚ) d := by
        show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ d) = jqNModC (AlgebraicClosure ℚ) d
        exact coeffMap_jqNModC _ d
      have hy : coeffMap A.subtype (jqNModC ↥A d) ∈ modularFunctionFieldBar M' := by
        rw [coeffMap_jqNModC, ← hid]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf
      obtain ⟨h, hval⟩ := hR₀ (jqNModC ↥A d) hy
      have hsub : (⟨⟨coeffMap A.subtype (jqNModC ↥A d), hy⟩, h⟩ : ↥R₀.integers) = ⟨_, hgi⟩ := by
        apply Subtype.ext; apply Subtype.ext
        show coeffMap A.subtype (jqNModC ↥A d) = coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ d jq)
        rw [coeffMap_jqNModC, hid]
      rw [hsub, coeffMap_jqNModC] at hval
      apply Subtype.ext
      show ((R₀.residue ⟨_, hgi⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) =
        ((ModularCurve.jqNFull (ResidueField ↥A) M' d hd : ↥(ModularCurve.modularFunctionFieldFullC (ResidueField ↥A) M')) :
          LaurentSeries (ResidueField ↥A))
      rw [hval, ModularCurve.coe_jqNFull]
    rw [← hfloor, hemb _ ⟨hgf, hgi, hcusp⟩ hgf hgi, val_apply]

#print axioms solution

end S_ModularCurve_FullLevel_Diamond_exists_algHom_modularFunctionFieldFullC_forall_apply_residue_eq_ringHom_of_transcendental_rigidDataH1Pow_of_tatePoint_pinGamma1
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_algHom_modularFunctionFieldFullC_forall_apply_residue_eq_ringHom_of_transcendental_rigidDataH1Pow_of_tatePoint_pinGamma1 (solution)
