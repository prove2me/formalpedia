-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_algHom_forall_apply_residue_eq_apply_of_eq_map_classify_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/82c0926b-270b-5bad-acac-0063ca7ed781

import Mathlib
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
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_ModularCurve_algebraMap_coeff_mem_of_mem_integers_of_cuspRegular
import Theorems.Thm_ModularCurve_exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular
import Theorems.Thm_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot
import Theorems.Thm_ModularCurve_FullLevel_residue_mem_toValuationSubring_of_cuspRegular_of_isRational
import Theorems.Thm_ModularCurve_FullLevel_Diamond_coeffEmb_mem_chartAlgFin_of_cuspRegular_of_mem_integers
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
import Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_algHom_forall_apply_residue_eq_apply_of_eq_map_classify_rigidDataH1Pow
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod instIsScalarTowerIntegralClosure"
p2m_attr_erase "instance" "instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve IsLocalRing

namespace ResidueFactorAux

local notation "Qb" => AlgebraicClosure ℚ

section Places

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem mem_of_ord_nonneg {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_nonneg_iff_mem (f : F) : 0 ≤ v.ord f ↔ f ∈ v.toValuationSubring :=
  ⟨mem_of_ord_nonneg v, ord_nonneg_of_mem v⟩

end Places

section Laurent

variable {L : Type*} [Field L] (A : ValuationSubring L)

def liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) : LaurentSeries A where
  coeff k := ⟨x.coeff k, hx k⟩
  isPWO_support' := by
    refine x.isPWO_support.mono ?_
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk ⊢
    intro h
    exact hk (Subtype.ext h)

@[scoped simp] theorem coeff_liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) (k : ℤ) :
    ((liftVal A x hx).coeff k : L) = x.coeff k := rfl

theorem coeffMap_subtype_liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) :
    coeffMap A.subtype (liftVal A x hx) = x := by
  ext k
  rfl

end Laurent

section FunctionField

variable (M' : ℕ) [NeZero M']

abbrev jF : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (modularFunctionField_le_full M' (jq_mem M'))⟩

abbrev jNF : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb Qb (jqN M'), coeffEmb_mem_laurentBaseChange Qb (jqd_mem_full M' (dvd_refl M'))⟩

theorem coeffEmb_jq_eq_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  map_jqModC (algebraMap ℚ L)

theorem coeffEmb_jqN_eq_jqNModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L (jqN M') = jqNModC L M' := by
  rw [jqNModC, ← coeffEmb_jq_eq_jqModC]
  exact ModularCurve.coeffMap_qExpand (algebraMap ℚ L) M' jq

theorem isIntegral_adjoin_jF_jNF :
    IsIntegral ↥(Algebra.adjoin Qb ({jF M'} : Set ↥(modularFunctionFieldBar M'))) (jNF M') := by
  obtain ⟨Φ⟩ := ModularCurve.nonempty_modularPolynomialData M'
  set R := Algebra.adjoin Qb ({jF M'} : Set ↥(modularFunctionFieldBar M')) with hR

  let jR : ↥R := ⟨jF M', Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let φ : Polynomial ℤ →+* ↥R := (Polynomial.aeval (R := ℤ) jR).toRingHom

  have hcompat : ((modularFunctionFieldBar M').val.toRingHom.comp ((algebraMap ↥R ↥(modularFunctionFieldBar M')).comp φ))
      = (coeffEmb Qb).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro n
      simp [φ, evalAtJ]
    · simp only [RingHom.coe_comp, Function.comp_apply, φ, evalAtJ_X]
      change (((Polynomial.aeval (R := ℤ) jR) Polynomial.X : ↥R) : ↥(modularFunctionFieldBar M')).1 = coeffEmb Qb jq
      rw [Polynomial.aeval_X]
  refine ⟨Φ.Φ.map φ, Φ.monic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  apply Subtype.val_injective
  change (modularFunctionFieldBar M').val.toRingHom (Polynomial.eval₂ ((algebraMap ↥R ↥(modularFunctionFieldBar M')).comp φ)
    (jNF M') Φ.Φ) = ((0 : ↥(modularFunctionFieldBar M')) : LaurentSeries Qb)
  rw [Polynomial.hom_eval₂, hcompat]
  change Polynomial.eval₂ ((coeffEmb Qb).comp evalAtJ) (coeffEmb Qb (jqN M')) Φ.Φ = 0
  rw [← Polynomial.hom_eval₂, Φ.eval_eq_zero, map_zero]

theorem ord_jNF_nonneg (P : Place Qb ↥(modularFunctionFieldBar M')) (hP : 0 ≤ P.ord (jF M')) :
    0 ≤ P.ord (jNF M') :=
  AlgebraicCurve.Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg P (isIntegral_adjoin_jF_jNF M') hP

theorem coe_algebraMap_bar (c : Qb) :
    ((algebraMap Qb ↥(modularFunctionFieldBar M') c : ↥(modularFunctionFieldBar M')) : LaurentSeries Qb) =
      algebraMap Qb (LaurentSeries Qb) c := rfl

end FunctionField

section OverQ

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} [hq : Fact q.Prime]

theorem isUnit_intCast_of_not_dvd (hA : A.LiesOverPrime q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    IsUnit ((n : ↥A)) := by
  have hcop : IsCoprime n (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right n q
    have hp : Nat.Prime q := hq.out
    rcases (Nat.dvd_prime hp).mp (by exact_mod_cast this : Int.gcd n q ∣ q) with h | h
    · exact h
    · exfalso; apply hn
      have h2 := Int.gcd_dvd_left n q
      rw [h] at h2
      exact h2
  obtain ⟨a, b, hab⟩ := hcop
  have hval : ¬ A.valuation (n : AlgebraicClosure ℚ) < 1 := by
    intro hlt
    have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
    have h1 : A.valuation ((a : AlgebraicClosure ℚ) * n + (b : AlgebraicClosure ℚ) * (q : ℕ)) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (intCast_mem A a))).trans_lt hlt
      · rw [Valuation.map_mul]
        exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (intCast_mem A b))).trans_lt hq1
    have h2 : (a : AlgebraicClosure ℚ) * n + (b : AlgebraicClosure ℚ) * (q : ℕ) = 1 := by
      exact_mod_cast hab
    rw [h2, Valuation.map_one] at h1
    exact lt_irrefl _ h1
  have hv1 : A.valuation (n : AlgebraicClosure ℚ) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (intCast_mem A n)) (not_lt.mp hval)
  have : ((n : ↥A) : AlgebraicClosure ℚ) = (n : AlgebraicClosure ℚ) := by simp
  rw [← this] at hv1
  exact (A.valuation_eq_one_iff _).mpr hv1

theorem natCast_q_mem_maximalIdeal (hA : A.LiesOverPrime q) : ((q : ↥A)) ∈ maximalIdeal ↥A := by
  rw [← ValuationSubring.coe_mem_nonunits_iff]
  simp at hA ⊢
  exact hA

theorem inv_natCast_q_not_mem (hA : A.LiesOverPrime q) : ((q : Qb))⁻¹ ∉ A := by
  intro h
  have hq0 : ((q : ℕ) : Qb) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hunit : IsUnit ((q : ↥A)) := by
    refine ⟨⟨(q : ↥A), ⟨((q : Qb))⁻¹, h⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · simp [mul_inv_cancel₀ hq0]
    · simp [inv_mul_cancel₀ hq0]
  exact (IsLocalRing.mem_maximalIdeal _).mp (natCast_q_mem_maximalIdeal hA) hunit

theorem residue_mem_bot_of_rat (hA : A.LiesOverPrime q) (r : ℚ) (hr : algebraMap ℚ Qb r ∈ A) :
    IsLocalRing.residue ↥A ⟨algebraMap ℚ Qb r, hr⟩ ∈ (⊥ : Subfield (ResidueField ↥A)) := by
  set a : ↥A := ⟨algebraMap ℚ Qb r, hr⟩ with ha

  have hrel : ((r.den : ℤ) : ↥A) * a = ((r.num : ℤ) : ↥A) := by
    apply Subtype.ext
    change (((r.den : ℤ) : ↥A) : Qb) * algebraMap ℚ Qb r = (((r.num : ℤ) : ↥A) : Qb)
    have h1 : (((r.den : ℤ) : ↥A) : Qb) = algebraMap ℚ Qb (r.den : ℚ) := by simp
    have h2 : (((r.num : ℤ) : ↥A) : Qb) = algebraMap ℚ Qb (r.num : ℚ) := by simp
    rw [h1, h2, ← map_mul, Rat.den_mul_eq_num]
  have hres := congrArg (IsLocalRing.residue ↥A) hrel
  rw [map_mul, map_intCast, map_intCast] at hres
  by_cases hden : (((r.den : ℤ) : ResidueField ↥A)) = 0
  ·
    exfalso
    have hnum0 : ((r.num : ℤ) : ResidueField ↥A) = 0 := by rw [← hres, hden, zero_mul]
    have hdvd : ∀ m : ℤ, ((m : ℤ) : ResidueField ↥A) = 0 → (q : ℤ) ∣ m := by
      intro m hm
      by_contra hnd
      have hu := isUnit_intCast_of_not_dvd hA m hnd
      rw [← map_intCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff] at hm
      exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
    have h1 : (q : ℤ) ∣ r.num := hdvd _ hnum0
    have h2 : (q : ℤ) ∣ (r.den : ℤ) := hdvd _ hden
    have hcop : IsCoprime r.num (r.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := r.reduced
      rw [Nat.Coprime] at this
      rw [Int.gcd, Int.natAbs_natCast]
      exact this
    have hqunit : IsUnit (q : ℤ) := hcop.isUnit_of_dvd' h1 h2
    have : (q : ℤ).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hqunit
    rw [Int.natAbs_natCast] at this
    exact hq.out.ne_one this
  · have : IsLocalRing.residue ↥A a = ((r.num : ℤ) : ResidueField ↥A) / ((r.den : ℤ) : ResidueField ↥A) := by
      rw [eq_div_iff hden, mul_comm, hres]
    rw [this]
    exact div_mem (intCast_mem _ _) (intCast_mem _ _)

end OverQ

section Admissible

variable (M' : ℕ) [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
  (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField ↥A) M'))

abbrev embB (gf : LaurentSeries ℚ) (h : gf ∈ modularFunctionFieldFull M') : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb Qb gf, coeffEmb_mem_laurentBaseChange Qb h⟩

def admissible : Subring (LaurentSeries ℚ) where
  carrier := {gf | ∃ h : gf ∈ modularFunctionFieldFull M', embB M' gf h ∈ R₀.integers ∧
    ∀ P : Place Qb ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb Qb gf, coeffEmb_mem_laurentBaseChange Qb h⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))}
  mul_mem' := by
    rintro f g ⟨hf, hfi, hfc⟩ ⟨hg, hgi, hgc⟩
    have hmem : f * g ∈ modularFunctionFieldFull M' := mul_mem hf hg
    have heq : embB M' (f * g) hmem = embB M' f hf * embB M' g hg := Subtype.ext (map_mul _ _ _)
    refine ⟨hmem, ?_, fun P hP => ?_⟩
    · rw [heq]; exact mul_mem hfi hgi
    · change 0 ≤ P.ord (embB M' (f * g) hmem)
      rw [heq, ord_nonneg_iff_mem]
      exact mul_mem ((ord_nonneg_iff_mem P _).mp (hfc P hP)) ((ord_nonneg_iff_mem P _).mp (hgc P hP))
  one_mem' := by
    have hmem : (1 : LaurentSeries ℚ) ∈ modularFunctionFieldFull M' := one_mem _
    have heq : embB M' 1 hmem = 1 := Subtype.ext (map_one _)
    refine ⟨hmem, ?_, fun P hP => ?_⟩
    · rw [heq]; exact one_mem _
    · change 0 ≤ P.ord (embB M' 1 hmem)
      rw [heq, Place.ord_one]
  add_mem' := by
    rintro f g ⟨hf, hfi, hfc⟩ ⟨hg, hgi, hgc⟩
    have hmem : f + g ∈ modularFunctionFieldFull M' := add_mem hf hg
    have heq : embB M' (f + g) hmem = embB M' f hf + embB M' g hg := Subtype.ext (map_add _ _ _)
    refine ⟨hmem, ?_, fun P hP => ?_⟩
    · rw [heq]; exact add_mem hfi hgi
    · change 0 ≤ P.ord (embB M' (f + g) hmem)
      rw [heq, ord_nonneg_iff_mem]
      exact add_mem ((ord_nonneg_iff_mem P _).mp (hfc P hP)) ((ord_nonneg_iff_mem P _).mp (hgc P hP))
  zero_mem' := by
    have hmem : (0 : LaurentSeries ℚ) ∈ modularFunctionFieldFull M' := zero_mem _
    have heq : embB M' 0 hmem = 0 := Subtype.ext (map_zero _)
    refine ⟨hmem, ?_, fun P hP => ?_⟩
    · rw [heq]; exact zero_mem _
    · change 0 ≤ P.ord (embB M' 0 hmem)
      rw [heq, Place.ord_zero]
  neg_mem' := by
    rintro f ⟨hf, hfi, hfc⟩
    have hmem : -f ∈ modularFunctionFieldFull M' := neg_mem hf
    have heq : embB M' (-f) hmem = -embB M' f hf := Subtype.ext (map_neg _ _)
    refine ⟨hmem, ?_, fun P hP => ?_⟩
    · rw [heq]; exact neg_mem hfi
    · change 0 ≤ P.ord (embB M' (-f) hmem)
      rw [heq, ord_nonneg_iff_mem]
      exact neg_mem ((ord_nonneg_iff_mem P _).mp (hfc P hP))

variable {M' R₀}

theorem memFull {gf : LaurentSeries ℚ} (h : gf ∈ admissible M' R₀) : gf ∈ modularFunctionFieldFull M' := by
  obtain ⟨h1, -, -⟩ := h; exact h1

theorem memInt {gf : LaurentSeries ℚ} (h : gf ∈ admissible M' R₀) : embB M' gf (memFull h) ∈ R₀.integers := by
  obtain ⟨h1, h2, -⟩ := h; exact h2

theorem memCusp {gf : LaurentSeries ℚ} (h : gf ∈ admissible M' R₀) :
    ∀ P : Place Qb ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
      0 ≤ P.ord ((⟨coeffEmb Qb gf, coeffEmb_mem_laurentBaseChange Qb (memFull h)⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) := by
  obtain ⟨h1, h2, h3⟩ := h; exact h3

variable (M' R₀)

def redHom : ↥(admissible M' R₀) →+* ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
  R₀.residue.comp
    ((((coeffEmb Qb).comp (admissible M' R₀).subtype).codRestrict (modularFunctionFieldBar M')
        (fun t => (embB M' (t : LaurentSeries ℚ) (memFull t.2)).2)).codRestrict R₀.integers
      (fun t => memInt t.2))

theorem redHom_apply (t : ↥(admissible M' R₀)) :
    redHom M' R₀ t = R₀.residue ⟨embB M' (t : LaurentSeries ℚ) (memFull t.2), memInt t.2⟩ := rfl

end Admissible

end ResidueFactorAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algHom_forall_apply_residue_eq_apply_of_eq_map_classify_rigidDataH1Pow.ResidueFactorAux"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_algHom_forall_apply_residue_eq_apply_of_eq_map_classify_rigidDataH1Pow.ResidueFactorAux"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open ResidueFactorAux

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
    (θ : (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) →+* (ResidueField ↥A))
    (hθ : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), θ (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a) =
      IsLocalRing.residue ↥A ⟨((a : ↥k₀) : AlgebraicClosure ℚ), ValuationSubring.mem_comap.mp a.2⟩)
    (S : Subalgebra (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M'))
    (hS : ∀ f : (modularFunctionFieldC (ResidueField ↥A) M'), f ∈ S ↔
      ∀ w : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M'), w.IsRational → jGeomGen (ResidueField ↥A) M' ∈ w.toValuationSubring → f ∈ w.toValuationSubring) :
    ∀ (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) (_ : y.IsMaximal)
        (ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), ψ c = 0 ↔ c ∈ y),
      ∃ χ : ↥S →ₐ[(ResidueField ↥A)] (ResidueField ↥A),
        ∀ (gf : LaurentSeries ℚ) (hgf : gf ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) gf, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hgf⟩ : ↥(modularFunctionFieldBar M')) :
              ↥(modularFunctionFieldBar M'))) →
          ∀ (hgK : (coeffEmb ↥k₀ gf) ∈ K)
            (hgC : (⟨_, hgK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
            ∃ hmem : (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField ↥A) M') ∈ S,
              χ ⟨R₀.residue ⟨_, hgi⟩, hmem⟩ = θ (ψ ⟨⟨_, hgK⟩, hgC⟩) := by
  classical

  intro y hy ψ hψ
  haveI hqfact : Fact q.Prime := inferInstance
  have hqprime : Nat.Prime q := Fact.out

  haveI hIAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField (ResidueField ↥A)
  haveI hCurve : IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M') :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) M'

  have hrat : ∀ u : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M'), u.IsRational := by
    intro u
    haveI : Module.Finite (ResidueField ↥A) u.ResidueField := IsCurveOver.finite_residueField u
    haveI : Algebra.IsIntegral (ResidueField ↥A) u.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField ↥A) (K := u.ResidueField)).2

  have hM'κ : ((M' : ℕ) : ResidueField ↥A) ≠ 0 := by
    intro h0
    have hu : IsUnit (((M' : ℤ)) : ↥A) :=
      isUnit_intCast_of_not_dvd hA (M' : ℤ) (by exact_mod_cast hqM')
    have h1 : IsLocalRing.residue ↥A (((M' : ℤ)) : ↥A) = 0 := by
      rw [map_intCast]; exact_mod_cast h0
    rw [IsLocalRing.residue_eq_zero_iff] at h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 hu

  let T : Subring (LaurentSeries ℚ) := admissible M' R₀

  have hjqT : jq ∈ T := by
    refine ⟨modularFunctionField_le_full M' (jq_mem M'), ?_, fun P hP => hP⟩

    have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [coeffMap_jqModC, ← coeffEmb_jq_eq_jqModC]; exact (jF M').2
    obtain ⟨h, -⟩ := hR₀ (jqModC ↥A) hy
    have heq : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : ↥(modularFunctionFieldBar M')) = jF M' := by
      apply Subtype.ext
      change coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq
      rw [coeffMap_jqModC, ← coeffEmb_jq_eq_jqModC]
    rw [heq] at h; exact h
  have hjqNT : jqN M' ∈ T := by
    refine ⟨jqd_mem_full M' (dvd_refl M'), ?_, fun P hP => ord_jNF_nonneg M' P hP⟩
    have hval : coeffMap A.subtype (jqNModC ↥A M') = coeffEmb (AlgebraicClosure ℚ) (jqN M') := by
      rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, coeffEmb_jqN_eq_jqNModC]; rfl
    have hy : coeffMap A.subtype (jqNModC ↥A M') ∈ modularFunctionFieldBar M' := by
      rw [hval]; exact (jNF M').2
    obtain ⟨h, -⟩ := hR₀ (jqNModC ↥A M') hy
    have heq : (⟨coeffMap A.subtype (jqNModC ↥A M'), hy⟩ : ↥(modularFunctionFieldBar M')) = jNF M' :=
      Subtype.ext hval
    rw [heq] at h; exact h

  let red : ↥T →+* ↥(modularFunctionFieldC (ResidueField ↥A) M') := redHom M' R₀
  have red_apply : ∀ t : ↥T, red t = R₀.residue ⟨embB M' (t : LaurentSeries ℚ) (memFull t.2), memInt t.2⟩ :=
    fun t => redHom_apply M' R₀ t

  have hcoefA : ∀ (t : ↥T) (n : ℤ), algebraMap ℚ (AlgebraicClosure ℚ) ((t : LaurentSeries ℚ).coeff n) ∈ A :=
    fun t n => ModularCurve.algebraMap_coeff_mem_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀
      (t : LaurentSeries ℚ) (memFull t.2) (memInt t.2) (memCusp t.2) n

  have red_coe : ∀ t : ↥T, ∃ (y : LaurentSeries ↥A), (∀ n, ((y.coeff n : ↥A) : AlgebraicClosure ℚ) =
      algebraMap ℚ (AlgebraicClosure ℚ) ((t : LaurentSeries ℚ).coeff n)) ∧
      ((red t : ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y := by
    intro t
    have hc : ∀ n, (coeffEmb (AlgebraicClosure ℚ) (t : LaurentSeries ℚ)).coeff n ∈ A := fun n => by
      rw [coeffEmb_coeff]; exact hcoefA t n
    refine ⟨liftVal A _ hc, fun n => rfl, ?_⟩
    have hyeq : coeffMap A.subtype (liftVal A _ hc) = coeffEmb (AlgebraicClosure ℚ) (t : LaurentSeries ℚ) :=
      coeffMap_subtype_liftVal A _ hc
    have hy : coeffMap A.subtype (liftVal A _ hc) ∈ modularFunctionFieldBar M' := by
      rw [hyeq]; exact (embB M' (t : LaurentSeries ℚ) (memFull t.2)).2
    obtain ⟨hint, hres⟩ := hR₀ _ hy
    have helt : (⟨⟨coeffMap A.subtype (liftVal A _ hc), hy⟩, hint⟩ : ↥R₀.integers) =
        ⟨embB M' (t : LaurentSeries ℚ) (memFull t.2), (memInt t.2)⟩ := Subtype.ext (Subtype.ext hyeq)
    rw [red_apply, ← helt, hres]

  have red_jq : red ⟨jq, hjqT⟩ = jGeomGen (ResidueField ↥A) M' := by
    apply Subtype.ext
    have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
      rw [coeffMap_jqModC, ← coeffEmb_jq_eq_jqModC]; exact (jF M').2
    obtain ⟨hint, hres⟩ := hR₀ (jqModC ↥A) hy
    have helt : (⟨⟨coeffMap A.subtype (jqModC ↥A), hy⟩, hint⟩ : ↥R₀.integers) =
        ⟨embB M' jq (modularFunctionField_le_full M' (jq_mem M')), (memInt hjqT)⟩ := by
      apply Subtype.ext; apply Subtype.ext
      change coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq
      rw [coeffMap_jqModC, ← coeffEmb_jq_eq_jqModC]
    rw [red_apply]
    change ((R₀.residue ⟨embB M' jq (modularFunctionField_le_full M' (jq_mem M')), (memInt hjqT)⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)
    rw [← helt, hres, coeffMap_jqModC]
  have red_jqN : red ⟨jqN M', hjqNT⟩ = jNGeomGen (ResidueField ↥A) M' := by
    apply Subtype.ext
    have hval : coeffMap A.subtype (jqNModC ↥A M') = coeffEmb (AlgebraicClosure ℚ) (jqN M') := by
      rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, coeffEmb_jqN_eq_jqNModC]; rfl
    have hy : coeffMap A.subtype (jqNModC ↥A M') ∈ modularFunctionFieldBar M' := by
      rw [hval]; exact (jNF M').2
    obtain ⟨hint, hres⟩ := hR₀ (jqNModC ↥A M') hy
    have helt : (⟨⟨coeffMap A.subtype (jqNModC ↥A M'), hy⟩, hint⟩ : ↥R₀.integers) =
        ⟨embB M' (jqN M') (jqd_mem_full M' (dvd_refl M')), (memInt hjqNT)⟩ :=
      Subtype.ext (Subtype.ext hval)
    rw [red_apply]
    change ((R₀.residue ⟨embB M' (jqN M') (jqd_mem_full M' (dvd_refl M')), (memInt hjqNT)⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) M')) : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M'
    rw [← helt, hres, jqNModC, coeffMap_qExpand, coeffMap_jqModC]; rfl

  have red_mem_S : ∀ t : ↥T, red t ∈ S := by
    intro t
    rw [red_apply, hS]
    intro w hw hjw
    exact ModularCurve.FullLevel.residue_mem_toValuationSubring_of_cuspRegular_of_isRational q M' hqM' A hA R₀ hR₀
      (t : LaurentSeries ℚ) (memFull t.2) (memInt t.2) (memCusp t.2) w hw hjw

  have hKmem : ∀ t : ↥T, coeffEmb ↥k₀ (t : LaurentSeries ℚ) ∈ K := by
    intro t
    rw [hK]
    have h1 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
      ↥k₀ M' 1 (q ^ 2 * M') ⟨q ^ 2, by ring⟩ H₁ (t : LaurentSeries ℚ) (memFull t.2)
    rwa [ModularCurve.qExpand_one_apply] at h1
  have hCmem : ∀ t : ↥T, (⟨_, hKmem t⟩ : ↥K) ∈
      AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by
    intro t
    exact ModularCurve.FullLevel.Diamond.coeffEmb_mem_chartAlgFin_of_cuspRegular_of_mem_integers q M' hqM' ℓg hℓg hℓg12 hℓgM'
      A hA W hW hle R₀ hR₀ s k₀ π₀ hπ hdvr hunif hhens hres hκ ξ hξ hιξ H₁ hH₁ K hK j hj
      (t : LaurentSeries ℚ) (memFull t.2) (memInt t.2) (memCusp t.2) (hKmem t)

  let sharp0 : ↥T →+* LaurentSeries ↥k₀ :=
    (coeffEmb ↥k₀).comp T.subtype
  let sharpK : ↥T →+* ↥K := sharp0.codRestrict K (fun t => hKmem t)
  let sharp : ↥T →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :=
    sharpK.codRestrict _ (fun t => hCmem t)
  let ρ : ↥T →+* ResidueField ↥A := θ.comp (ψ.toRingHom.comp sharp)
  have ρ_apply : ∀ t : ↥T, ρ t = θ (ψ ⟨⟨_, hKmem t⟩, hCmem t⟩) := fun t => rfl

  have hqκ : ((q : ℕ) : ResidueField ↥A) = 0 := by
    have : ((q : ℕ) : ResidueField ↥A) = IsLocalRing.residue ↥A ((q : ↥A)) := by rw [map_natCast]
    rw [this, IsLocalRing.residue_eq_zero_iff]
    exact natCast_q_mem_maximalIdeal hA
  have hker : ∀ t : ↥T, red t = 0 → ρ t = 0 := by
    intro t ht
    rw [red_apply] at ht
    obtain ⟨g', hg', hgi', hcusp', heq⟩ :=
      ModularCurve.exists_eq_natCast_mul_of_residue_eq_zero_of_mem_integers_of_cuspRegular q M' A hA R₀ hR₀
        (t : LaurentSeries ℚ) (memFull t.2) (memInt t.2) (memCusp t.2) ht
    have ht' : g' ∈ T := ⟨hg', hgi', hcusp'⟩
    have hteq : t = (q : ↥T) * ⟨g', ht'⟩ := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_natCast]
      exact heq
    rw [hteq, map_mul, map_natCast, hqκ, zero_mul]

  let cfun : ℤ → (↥(modularFunctionFieldC (ResidueField ↥A) M') →ₗ[ResidueField ↥A] ResidueField ↥A) := fun n =>
    { toFun := fun f => (f : LaurentSeries (ResidueField ↥A)).coeff n
      map_add' := fun f g => by simp
      map_smul' := fun c f => by
        rw [RingHom.id_apply, IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
          HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul] }
  have cfun_apply : ∀ n f, cfun n f = (f : LaurentSeries (ResidueField ↥A)).coeff n := fun n f => rfl
  have hsep : ∀ b : ↥(modularFunctionFieldC (ResidueField ↥A) M'), (∀ n, cfun n b = 0) → b = 0 := by
    intro b hb
    apply Subtype.ext
    ext n
    simpa [cfun_apply] using hb n
  have hbot : ∀ (t : ↥T) (n : ℤ), cfun n (red t) ∈ (⊥ : Subfield (ResidueField ↥A)) := by
    intro t n
    obtain ⟨yv, hyv, hred⟩ := red_coe t
    rw [cfun_apply, hred, coeffMap_coeff]
    have : yv.coeff n = ⟨algebraMap ℚ (AlgebraicClosure ℚ) ((t : LaurentSeries ℚ).coeff n), hcoefA t n⟩ :=
      Subtype.ext (hyv n)
    rw [this]
    exact residue_mem_bot_of_rat hA _ (hcoefA t n)

  obtain ⟨χ₁, hχ₁⟩ := Algebra.exists_algHom_adjoin_range_apply_eq_of_forall_apply_mem_bot cfun hsep red ρ hbot hker
  have hS₁S : Algebra.adjoin (ResidueField ↥A) (Set.range red) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨t, rfl⟩
    exact red_mem_S t

  have hR₂S₁ : Algebra.adjoin (ResidueField ↥A) ({jGeomGen (ResidueField ↥A) M', jNGeomGen (ResidueField ↥A) M'} :
      Set ↥(modularFunctionFieldC (ResidueField ↥A) M')) ≤ Algebra.adjoin (ResidueField ↥A) (Set.range red) := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rcases hx with hx | hx
    · rw [hx, ← red_jq]; exact Algebra.subset_adjoin (Set.mem_range_self _)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← red_jqN]; exact Algebra.subset_adjoin (Set.mem_range_self _)
  have hSint : ∀ f : ↥(modularFunctionFieldC (ResidueField ↥A) M'), f ∈ S →
      IsIntegral ↥(Algebra.adjoin (ResidueField ↥A) ({jGeomGen (ResidueField ↥A) M', jNGeomGen (ResidueField ↥A) M'} :
        Set ↥(modularFunctionFieldC (ResidueField ↥A) M'))) f := by
    intro f hf
    refine (ModularCurve.forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin (N := M') (k := ResidueField ↥A) hM'κ f).mp ?_
    intro u hu
    exact (hS f).mp hf u (hrat u) hu.1

  letI algS : Algebra ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) ↥S :=
    (Subalgebra.inclusion hS₁S).toRingHom.toAlgebra
  have algS_apply : ∀ x : ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)),
      algebraMap ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) ↥S x = Subalgebra.inclusion hS₁S x := fun x => rfl
  haveI : Algebra.IsIntegral ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) ↥S := by
    refine ⟨fun f => ?_⟩
    obtain ⟨p, hpm, hp0⟩ := hSint (f : ↥(modularFunctionFieldC (ResidueField ↥A) M')) f.2
    refine ⟨p.map (Subalgebra.inclusion hR₂S₁).toRingHom, hpm.map _, ?_⟩
    apply Subtype.val_injective
    change S.val.toRingHom (Polynomial.eval₂ (algebraMap ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) ↥S) f
      (p.map (Subalgebra.inclusion hR₂S₁).toRingHom)) = ((0 : ↥S) : ↥(modularFunctionFieldC (ResidueField ↥A) M'))
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
    have hcomp : (S.val.toRingHom.comp (algebraMap ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) ↥S)).comp
        (Subalgebra.inclusion hR₂S₁).toRingHom =
        algebraMap ↥(Algebra.adjoin (ResidueField ↥A) ({jGeomGen (ResidueField ↥A) M', jNGeomGen (ResidueField ↥A) M'} :
          Set ↥(modularFunctionFieldC (ResidueField ↥A) M'))) ↥(modularFunctionFieldC (ResidueField ↥A) M') := by
      ext x; rfl
    rw [hcomp]
    exact hp0

  have hkerle : RingHom.ker (algebraMap ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) ↥S) ≤ RingHom.ker χ₁.toRingHom := by
    intro x hx
    rw [RingHom.mem_ker, algS_apply] at hx
    have : x = 0 := by
      apply Subtype.ext
      have := congrArg Subtype.val hx
      exact this
    rw [this]; exact (RingHom.ker _).zero_mem
  obtain ⟨χ', hχ'⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed χ₁.toRingHom hkerle
  have hχ'_apply : ∀ x : ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)), χ' (Subalgebra.inclusion hS₁S x) = χ₁ x := by
    intro x
    have := congrArg (fun φ : ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) →+* ResidueField ↥A => φ x) hχ'
    exact this
  let χ : ↥S →ₐ[ResidueField ↥A] ResidueField ↥A :=
    { χ' with
      commutes' := fun c => by
        have h1 : algebraMap (ResidueField ↥A) ↥S c =
            Subalgebra.inclusion hS₁S (algebraMap (ResidueField ↥A) ↥(Algebra.adjoin (ResidueField ↥A) (Set.range red)) c) :=
          Subtype.ext rfl
        change χ' (algebraMap (ResidueField ↥A) ↥S c) = c
        rw [h1, hχ'_apply, AlgHom.commutes]; rfl }

  refine ⟨χ, ?_⟩
  intro gf hgf hgi hcusp hgK hgC
  have ht : gf ∈ T := ⟨hgf, hgi, hcusp⟩
  refine ⟨red_mem_S ⟨gf, ht⟩, ?_⟩
  have hmemS₁ : red ⟨gf, ht⟩ ∈ Algebra.adjoin (ResidueField ↥A) (Set.range red) :=
    Algebra.subset_adjoin (Set.mem_range_self _)
  have h1 : (⟨R₀.residue ⟨_, hgi⟩, red_mem_S ⟨gf, ht⟩⟩ : ↥S) = Subalgebra.inclusion hS₁S ⟨red ⟨gf, ht⟩, hmemS₁⟩ :=
    Subtype.ext rfl
  change χ' ⟨R₀.residue ⟨_, hgi⟩, red_mem_S ⟨gf, ht⟩⟩ = θ (ψ ⟨⟨_, hgK⟩, hgC⟩)
  rw [h1, hχ'_apply, hχ₁ ⟨gf, ht⟩]
  exact ρ_apply ⟨gf, ht⟩

#print axioms solution

end S_ModularCurve_FullLevel_Diamond_exists_algHom_forall_apply_residue_eq_apply_of_eq_map_classify_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_algHom_forall_apply_residue_eq_apply_of_eq_map_classify_rigidDataH1Pow (solution)
