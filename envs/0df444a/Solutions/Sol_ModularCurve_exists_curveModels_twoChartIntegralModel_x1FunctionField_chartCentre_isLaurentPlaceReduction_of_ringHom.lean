-- Prove2me | solution 1 for ModularCurve.exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/958f0333-0795-568e-9a0c-73026b20fc5c

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
import Theorems.Thm_ModularCurve_exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_CurveModel_existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
import Theorems.Thm_ModularCurve_exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois TateModule.instModule TateModule.instSMul AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve~coeffMap_injective P2MW.S_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "IsLaurentPlaceReduction IsPlaceReductionQExpModL qExpFunctionFieldC x1FunctionFieldC x1FunctionField arithmeticGalois coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd JOneES.exists_transcendental_finiteDimensional_laurentBaseChange transcendental_jqModC exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd mem_of_coeffMap_mem_adjoin_image_of_ringHom qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC isCurveOver_qExpFunctionFieldC_of_isAlgClosed"
namespace FibreCurveModelsGlue
p2m_open "ModularCurve~coeffMap_injective"

section TwoChart

universe u

open AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem span_overlap_aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ Z) (y : Y) (z : Z)
    (k : WalkingSpan) (fi : k ⟶ WalkingSpan.left) (fj : k ⟶ WalkingSpan.right)
    (w : (span f g).obj k) (h₁ : (span f g).map fi w = y) (h₂ : (span f g).map fj w = z) :
    ∃ x : X, f.base x = y ∧ g.base x = z := by
  match k, fi, fj, w, h₁, h₂ with
  | none, WidePushoutShape.Hom.init _, WidePushoutShape.Hom.init _, w, h₁, h₂ => exact ⟨w, h₁, h₂⟩

theorem ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    exact span_overlap_aux _ _ _ _ k fi fj w h₁ h₂
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w = (fInf R F j ≫ ιInf R F j).base w
    rw [glue_condition]

theorem range_fInf : Set.range (fInf R F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R F j))) :
      Set (PrimeSpectrum (chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jInvChartInf R F j)

theorem range_fFin : Set.range (fFin R F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R F j))) :
      Set (PrimeSpectrum (chartAlgFin R F j))) := by
  letI := (inclFin R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R F j) (jChartFin R F j)

theorem ιInf_mem_range_ιFin_iff (xi : XInf R F j) :
    (ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔ jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem ιFin_mem_range_ιInf_iff (x₀ : XFin R F j) :
    (ιFin R F j).base x₀ ∈ Set.range (ιInf R F j).base ↔ jChartFin R F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp h.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fInf R F j).base w, ((ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩).symm⟩

variable {R F j}

theorem exists_eq_specMap_comp_ιFin {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (h : g.base (closedPoint O) ∈ Set.range (ιFin R F j).base) :
    ∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j := by
  have hmem : g.base (closedPoint O) ∈ (ιFin R F j).opensRange := h
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem g hmem
  have hrange : Set.range g.base ⊆ Set.range (ιFin R F j).base := by
    rintro _ ⟨s, rfl⟩
    have : s ∈ g ⁻¹ᵁ (ιFin R F j).opensRange := by rw [htop]; trivial
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιFin R F j) g hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_eq_specMap_comp_ιInf {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    (h : g.base (closedPoint O) ∈ Set.range (ιInf R F j).base) :
    ∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j := by
  have hmem : g.base (closedPoint O) ∈ (ιInf R F j).opensRange := h
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem g hmem
  have hrange : Set.range g.base ⊆ Set.range (ιInf R F j).base := by
    rintro _ ⟨s, rfl⟩
    have : s ∈ g ⁻¹ᵁ (ιInf R F j).opensRange := by rw [htop]; trivial
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift (ιInf R F j) g hrange)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_chart_factorisation_fin {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) :
    (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j) ∨
      (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j ∧
        β (jInvChartInf R F j) ∈ maximalIdeal O) := by
  by_cases h : g.base (closedPoint O) ∈ Set.range (ιFin R F j).base
  · exact Or.inl (exists_eq_specMap_comp_ιFin g h)
  · obtain ⟨β, hβ⟩ := exists_eq_specMap_comp_ιInf g
      ((mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_left h)
    refine Or.inr ⟨β, hβ, ?_⟩
    by_contra hnot
    apply h
    rw [hβ, Scheme.Hom.comp_base, TopCat.comp_app]
    refine (ιInf_mem_range_ιFin_iff R F j _).mpr ?_
    rw [Spec.map_apply]
    exact hnot

theorem exists_chart_factorisation_inf {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) :
    (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j) ∨
      (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j ∧
        β (jChartFin R F j) ∈ maximalIdeal O) := by
  by_cases h : g.base (closedPoint O) ∈ Set.range (ιInf R F j).base
  · exact Or.inl (exists_eq_specMap_comp_ιInf g h)
  · obtain ⟨β, hβ⟩ := exists_eq_specMap_comp_ιFin g
      ((mem_range_ιFin_or_mem_range_ιInf R F j _).resolve_right h)
    refine Or.inr ⟨β, hβ, ?_⟩
    by_contra hnot
    apply h
    rw [hβ, Scheme.Hom.comp_base, TopCat.comp_app]
    refine (ιFin_mem_range_ιInf_iff R F j _).mpr ?_
    rw [Spec.map_apply]
    exact hnot

theorem exists_chart_factorisation {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j) :
    (∃ β : chartAlgFin R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιFin R F j) ∨
      (∃ β : chartAlgInf R F j →+* O, g = Spec.map (CommRingCat.ofHom β) ≫ ιInf R F j) := by
  rcases exists_chart_factorisation_fin g with h | ⟨β, hβ, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨β, hβ⟩

end TwoChart

section Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_mem_nonunits {O : ValuationSubring F} {x : F} (hx : x ∈ O.nonunits) : x ∈ O :=
  O.nonunits_subset hx

theorem sub_mem_nonunits {O : ValuationSubring F} {x y : F} (hx : x ∈ O.nonunits)
    (hy : y ∈ O.nonunits) : x - y ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hx hy ⊢
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  exact ⟨sub_mem hx hy, Ideal.sub_mem _ hx' hy'⟩

theorem false_of_mem_of_inv_mem_nonunits {O : ValuationSubring F} {u : F} (hu0 : u ≠ 0)
    (hu : u ∈ O) (hui : u⁻¹ ∈ O.nonunits) : False := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hui
  obtain ⟨hui, hm⟩ := hui
  have hunit : IsUnit (⟨u⁻¹, hui⟩ : O) :=
    IsUnit.of_mul_eq_one ⟨u, hu⟩ (Subtype.ext (inv_mul_cancel₀ hu0))
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp hm) hunit

theorem eq_zero_of_algebraMap_mem_nonunits (P : Place K F) {c : K}
    (hc : algebraMap K F c ∈ P.toValuationSubring.nonunits) : c = 0 := by
  by_contra h0
  refine false_of_mem_of_inv_mem_nonunits (O := P.toValuationSubring)
    (u := algebraMap K F c⁻¹) ?_ (P.algebraMap_mem' _) ?_
  · rw [map_inv₀]; exact inv_ne_zero ((map_ne_zero _).mpr h0)
  · rwa [map_inv₀, inv_inv]

theorem const_eq_of_sub_mem_nonunits (P : Place K F) {f : F} {c d : K}
    (hc : f - algebraMap K F c ∈ P.toValuationSubring.nonunits)
    (hd : f - algebraMap K F d ∈ P.toValuationSubring.nonunits) : c = d := by
  have h := sub_mem_nonunits hd hc
  rw [sub_sub_sub_cancel_left, ← map_sub] at h
  exact (sub_eq_zero.mp (eq_zero_of_algebraMap_mem_nonunits P h))

theorem mem_of_sub_algebraMap_mem_nonunits (P : Place K F) {f : F} {c : K}
    (hc : f - algebraMap K F c ∈ P.toValuationSubring.nonunits) : f ∈ P.toValuationSubring := by
  have h := add_mem (mem_of_mem_nonunits hc) (P.algebraMap_mem' c)
  rwa [sub_add_cancel] at h

end Valuation

section Coeff

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff n) h
  simpa only [coeffMap_coeff] using this

end Coeff

end ModularCurve.FibreCurveModelsGlue

end

namespace K23c
namespace POP

universe u

theorem stalkClosedPointTo_germ_congr {K : Type u} [Field K] {Y : Scheme.{u}}
    (F₁ F₂ : Spec (CommRingCat.of K) ⟶ Y) (hF : F₁ = F₂) (W : Y.Opens) (t : Γ(Y, W))
    (h₁ : F₁.base (IsLocalRing.closedPoint K) ∈ W) (h₂ : F₂.base (IsLocalRing.closedPoint K) ∈ W) :
    (Scheme.stalkClosedPointTo F₁).hom ((Y.presheaf.germ W _ h₁).hom t) =
      (Scheme.stalkClosedPointTo F₂).hom ((Y.presheaf.germ W _ h₂).hom t) := by
  subst hF; rfl

theorem stalkClosedPointTo_germ_app {K : Type u} [Field K] {X Y : Scheme.{u}}
    (p : Spec (CommRingCat.of K) ⟶ X) (g : X ⟶ Y) (W : Y.Opens) (t : Γ(Y, W))
    (hx : g.base (p.base (IsLocalRing.closedPoint K)) ∈ W) :
    (Scheme.stalkClosedPointTo p).hom
        ((X.presheaf.germ (g ⁻¹ᵁ W) (p.base (IsLocalRing.closedPoint K)) hx).hom ((g.app W).hom t)) =
      (Scheme.stalkClosedPointTo (p ≫ g)).hom ((Y.presheaf.germ W ((p ≫ g).base (IsLocalRing.closedPoint K)) hx).hom t) := by
  rw [← Scheme.Hom.germ_stalkMap_apply g W (p.base (IsLocalRing.closedPoint K)) hx t, Scheme.stalkClosedPointTo_comp]
  rfl

theorem stalkClosedPointTo_specMap_comp {K : Type u} [Field K] {A : CommRingCat.{u}} {Y : Scheme.{u}}
    (ι : Spec A ⟶ Y) [IsOpenImmersion ι] (ψ : A ⟶ CommRingCat.of K) (b : A)
    (h : ι.base ((Spec.map ψ).base (IsLocalRing.closedPoint K)) ∈ ι ''ᵁ ⊤) :
    (Scheme.stalkClosedPointTo (Spec.map ψ ≫ ι)).hom
        ((Y.presheaf.germ (ι ''ᵁ ⊤) ((Spec.map ψ ≫ ι).base (IsLocalRing.closedPoint K)) h).hom
          ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b))) = ψ b := by
  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (Spec.map ψ)).hom ((ι.stalkMap ((Spec.map ψ).base (IsLocalRing.closedPoint K))).hom
    ((Y.presheaf.germ (ι ''ᵁ ⊤) (ι.base ((Spec.map ψ).base (IsLocalRing.closedPoint K))) h).hom
      ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv b)))) = ψ b
  rw [Scheme.Hom.germ_stalkMap_apply ι (ι ''ᵁ ⊤) ((Spec.map ψ).base (IsLocalRing.closedPoint K)) h,
    ← CommRingCat.comp_apply (ι.appIso ⊤).inv, Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply',
    ← CommRingCat.comp_apply _ (Scheme.stalkClosedPointTo (Spec.map ψ)), Scheme.germ_stalkClosedPointTo_Spec,
    CommRingCat.comp_apply, Iso.inv_hom_id_apply]

theorem sub_mem_nonunits_of_residue_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (c : K)
    (h : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField c) :
    f - algebraMap K F c ∈ v.toValuationSubring.nonunits := by
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hsub : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf hc
  have hx : (⟨f - algebraMap K F c, hsub⟩ : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap K v.toValuationSubring c :=
    Subtype.ext rfl
  have hmax : (⟨f - algebraMap K F c, hsub⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    rw [← IsLocalRing.residue_eq_zero_iff, hx, map_sub, h, sub_eq_zero]
    rfl
  exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f - algebraMap K F c, hsub⟩)).mpr hmax

end K23c.POP

open scoped MatrixGroups in
p2m_open "ModularCurve~coeffMap_injective" in open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom.ModularCurve IsLocalRing ModularCurve.FibreCurveModelsGlue AlgebraicCurve.TwoChartIntegralModel in

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (j : ↥(ModularCurve.x1FunctionField M)) [Fact (j ≠ 0)] (hj : ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (πk : ↥Pl →+* k) :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))
      (eη : Mη.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eη)
      (_ : eη ≫ pullback.snd _ _ = Mη.toBase)

      (_ : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* (AlgebraicClosure ℚ)),
        x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
          (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
            algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) (β b) ∈ (Mη.pointEquivPlace x).toValuationSubring.nonunits)
      (_ : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* (AlgebraicClosure ℚ)),
        x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
          (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
            algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) (β b) ∈ (Mη.pointEquivPlace x).toValuationSubring.nonunits)

      (_ : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst _ _ →
        Mη.pointEquivPlace x' = ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField M) σ • Mη.pointEquivPlace x)

      (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl) (_ : Pl.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))

      (Mdl : CurveModel k ↥(ModularCurve.x1FunctionFieldC k M))
      (e : Mdl.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))))
      (_ : IsIso e) (_ : e ≫ pullback.snd _ _ = Mdl.toBase)

      (πFin : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M)) (πInf : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M))
      (_ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), ∃ yb : LaurentSeries ↥Pl,
        ModularCurve.coeffMap Pl.subtype yb = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ∧
          ((πFin b : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk yb)
      (_ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), ∃ yb : LaurentSeries ↥Pl,
        ModularCurve.coeffMap Pl.subtype yb = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ∧
          ((πInf b : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk yb)

      (_ : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* k),
        y.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πFin b - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (β b) ∈ (Mdl.pointEquivPlace y).toValuationSubring.nonunits)
      (_ : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* k),
        y.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πInf b - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (β b) ∈ (Mdl.pointEquivPlace y).toValuationSubring.nonunits)

      (r : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) → Place k ↥(ModularCurve.x1FunctionFieldC k M)),
      ModularCurve.IsLaurentPlaceReduction Pl πk (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionFieldC k M) r ∧

      ∀ (xA : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ₀)) (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : {q : Spec (CommRingCat.of k) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}),
        x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ xA.1 →
        y.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ xA.1 →
        Mdl.pointEquivPlace y = r (Mη.pointEquivPlace x) := by
  classical

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  let jb : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) j.2⟩
  have hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) := rfl
  have hjbq : (jb : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hjb, hj]
    exact map_jqModC _
  have htrans : Transcendental (AlgebraicClosure ℚ) jb := by
    have h := ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)
    rw [← hjbq] at h
    exact (transcendental_algebraMap_iff (algebraMap ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) (LaurentSeries (AlgebraicClosure ℚ))).injective).mp h
  haveI : Fact (jb ≠ 0) := ⟨fun h => htrans (by rw [h]; exact isAlgebraic_zero)⟩
  haveI hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := by
    have h18 : ∃ x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)), Transcendental (AlgebraicClosure ℚ) x ∧ FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) hT
    obtain ⟨x, -, hx⟩ := h18
    haveI := hx
    exact AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x htrans
  haveI : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) := by
    rw [CurveModel.adjoin_simple_inv_eq]; exact hfd

  obtain ⟨eη, hiso, heη, hcFin, hcInf, hgal⟩ :=
    ModularCurve.exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
      (ModularCurve.x1FunctionField M) p j jb hjb htrans
  obtain ⟨ρ₀, hρ₀, ι, hιπ, M₀, e₀, hiso₀, he₀, hne₀, hread₀, hne₀Inf, hread₀Inf, Mk, ek, hisoK, hek, hnek, hreadK, hnekInf, hreadKInf, g, hg, hgcomp, ψ, hψ, hsq⟩ :=
    ModularCurve.exists_curveModels_fibres_twoChartIntegralModel_x1FunctionField_readCharts_and_iso_pullback_of_ringHom
      p M hpM j hj Pl hPl k πk
  haveI := hiso
  haveI := hisoK
  haveI := hiso₀

  obtain ⟨πFin, πInf, hπFin_def, hπInf_def, hqFin, hqInf⟩ : ∃ (πFin : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M)) (πInf : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M)),
      (haveI := hnek; ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πFin b = Mk.ffEquiv.symm (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
            (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) ∧
      (haveI := hnekInf; ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πInf b = Mk.ffEquiv.symm (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
            (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), ∃ yb : LaurentSeries ↥Pl,
        ModularCurve.coeffMap Pl.subtype yb = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ∧
          ((πFin b : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk yb) ∧
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), ∃ yb : LaurentSeries ↥Pl,
        ModularCurve.coeffMap Pl.subtype yb = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ∧
          ((πInf b : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk yb) := by

    haveI hjfact' : Fact (@Ne (↥(ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) j 0) := ⟨fun h => (Fact.out : j ≠ 0) h⟩
    obtain ⟨ρ', -, Ms', es', -, -, πFin', πInf', hS'⟩ :=
      ModularCurve.exists_curveModel_specialFibreIso_twoChartIntegralModel_qExpFunctionFieldC_chartCentre_of_not_dvd
        M (CongruenceSubgroup.Gamma1 M) le_rfl (CongruenceSubgroup.Gamma1_in_Gamma0 M) p hpM j hj
    obtain ⟨hliftFin, hliftInf, -⟩ := hS' Pl hPl
    haveI := hnek
    haveI := hnekInf
    let πFin : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M) :=
      (Mk.ffEquiv.symm : _ ≃+* _).toRingHom.comp
        ((Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))).hom.comp
          ((((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)).appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv.hom)))
    let πInf : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M) :=
      (Mk.ffEquiv.symm : _ ≃+* _).toRingHom.comp
        ((Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))).hom.comp
          ((((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)).appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv.hom)))
    refine ⟨πFin, πInf, fun _ => rfl, fun _ => rfl, fun b => ?_, fun b => ?_⟩
    · obtain ⟨yb, h1, -⟩ := hliftFin b
      exact ⟨yb, h1, hreadK b yb h1⟩
    · obtain ⟨yb, h1, -⟩ := hliftInf b
      exact ⟨yb, h1, hreadKInf b yb h1⟩

  have hcenFin : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ Mk.C // q ≫ Mk.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* k),
      y.1 ≫ ek ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
      ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πFin b - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (β b) ∈ (Mk.pointEquivPlace y).toValuationSubring.nonunits := by
    intro y β hy b

    have hwV : (Spec.map (CommRingCat.ofHom β) ≫ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)).base (IsLocalRing.closedPoint k) ∈ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤) :=
      ⟨(Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint k), trivial, rfl⟩
    have hx₀U : (ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).base (y.1.base (IsLocalRing.closedPoint k)) ∈ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤) := by
      rw [← Scheme.Hom.comp_apply, hy]; exact hwV
    obtain ⟨sx, hread, hev⟩ : ∃ sx : Mk.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k)),
        Mk.ffEquiv.symm (algebraMap _ Mk.C.functionField sx) =
          Mk.ffEquiv.symm (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
            (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b)))) ∧
        (Scheme.stalkClosedPointTo y.1).hom sx = β b := by
      refine ⟨(Mk.C.presheaf.germ ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint k)) hx₀U).hom
        (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))), ?_, ?_⟩
      · change Mk.ffEquiv.symm ((Mk.C.presheaf.stalkSpecializes ((genericPoint_spec Mk.C).specializes trivial)).hom _) = _
        congr 1
        exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
      · rw [K23c.POP.stalkClosedPointTo_germ_app, K23c.POP.stalkClosedPointTo_germ_congr _ _ hy _ _ _ hwV]
        exact K23c.POP.stalkClosedPointTo_specMap_comp (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (CommRingCat.ofHom β) b hwV
    obtain ⟨hmem, hres, -⟩ :=
      AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo Mk y sx
    rw [hev] at hres
    haveI := hnek
    rw [hπFin_def b, ← hread]
    exact K23c.POP.sub_mem_nonunits_of_residue_eq _ hmem _ hres
  have hcenInf : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ Mk.C // q ≫ Mk.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* k),
      y.1 ≫ ek ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
      ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πInf b - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (β b) ∈ (Mk.pointEquivPlace y).toValuationSubring.nonunits := by
    intro y β hy b

    have hwV : (Spec.map (CommRingCat.ofHom β) ≫ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)).base (IsLocalRing.closedPoint k) ∈ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤) :=
      ⟨(Spec.map (CommRingCat.ofHom β)).base (IsLocalRing.closedPoint k), trivial, rfl⟩
    have hx₀U : (ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).base (y.1.base (IsLocalRing.closedPoint k)) ∈ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤) := by
      rw [← Scheme.Hom.comp_apply, hy]; exact hwV
    obtain ⟨sx, hread, hev⟩ : ∃ sx : Mk.C.presheaf.stalk (y.1.base (IsLocalRing.closedPoint k)),
        Mk.ffEquiv.symm (algebraMap _ Mk.C.functionField sx) =
          Mk.ffEquiv.symm (Mk.C.germToFunctionField ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
            (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b)))) ∧
        (Scheme.stalkClosedPointTo y.1).hom sx = β b := by
      refine ⟨(Mk.C.presheaf.germ ((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)) (y.1.base (IsLocalRing.closedPoint k)) hx₀U).hom
        (((ek ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))), ?_, ?_⟩
      · change Mk.ffEquiv.symm ((Mk.C.presheaf.stalkSpecializes ((genericPoint_spec Mk.C).specializes trivial)).hom _) = _
        congr 1
        exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
      · rw [K23c.POP.stalkClosedPointTo_germ_app, K23c.POP.stalkClosedPointTo_germ_congr _ _ hy _ _ _ hwV]
        exact K23c.POP.stalkClosedPointTo_specMap_comp (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (CommRingCat.ofHom β) b hwV
    obtain ⟨hmem, hres, -⟩ :=
      AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo Mk y sx
    rw [hev] at hres
    haveI := hnekInf
    rw [hπInf_def b, ← hread]
    exact K23c.POP.sub_mem_nonunits_of_residue_eq _ hmem _ hres

  obtain ⟨r, hr, hvFinK, hvInfK⟩ : ∃ r : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) → Place k ↥(ModularCurve.x1FunctionFieldC k M),
      ModularCurve.IsLaurentPlaceReduction Pl πk (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionFieldC k M) r ∧
      (∀ (P : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥Pl),
        (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
            algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) ((β b : ↥Pl) : AlgebraicClosure ℚ) ∈ P.toValuationSubring.nonunits) →
        ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (yb : LaurentSeries ↥Pl) (bbar : ↥(ModularCurve.x1FunctionFieldC k M)),
          coeffMap Pl.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
          (bbar : LaurentSeries k) = coeffMap πk yb →
          bbar - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (πk (β b)) ∈ (r P).toValuationSubring.nonunits) ∧
      (∀ (P : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥Pl),
        (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
            algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) ((β b : ↥Pl) : AlgebraicClosure ℚ) ∈ P.toValuationSubring.nonunits) →
        ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (yb : LaurentSeries ↥Pl) (bbar : ↥(ModularCurve.x1FunctionFieldC k M)),
          coeffMap Pl.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
          (bbar : LaurentSeries k) = coeffMap πk yb →
          bbar - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (πk (β b)) ∈ (r P).toValuationSubring.nonunits) := by

    haveI : IsAlgClosed (IsLocalRing.ResidueField ↥Pl) := ValuationSubring.isAlgClosed_residueField Pl
    haveI hjfact : Fact (@Ne (↥(ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) j 0) := ⟨fun h => (Fact.out : j ≠ 0) h⟩
    have h3d : ∃ r₀ : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) → Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M),
        ModularCurve.IsPlaceReductionQExpModL Pl (CongruenceSubgroup.Gamma1 M) r₀ ∧
        (∀ (P : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥Pl),
          (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
            (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
              algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) ((β b : ↥Pl) : AlgebraicClosure ℚ) ∈ P.toValuationSubring.nonunits) →
          ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (yb : LaurentSeries ↥Pl) (bbar : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)),
            coeffMap Pl.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
            (bbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yb →
            bbar - algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) (IsLocalRing.residue ↥Pl (β b)) ∈ (r₀ P).toValuationSubring.nonunits) ∧
        (∀ (P : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥Pl),
          (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
            (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
              algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) ((β b : ↥Pl) : AlgebraicClosure ℚ) ∈ P.toValuationSubring.nonunits) →
          ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)) (yb : LaurentSeries ↥Pl) (bbar : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)),
            coeffMap Pl.subtype yb = coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) →
            (bbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = coeffMap (IsLocalRing.residue ↥Pl) yb →
            bbar - algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) (IsLocalRing.residue ↥Pl (β b)) ∈ (r₀ P).toValuationSubring.nonunits) :=
      ModularCurve.exists_isPlaceReductionQExpModL_chartCentre_of_not_dvd M (CongruenceSubgroup.Gamma1 M) le_rfl
        (CongruenceSubgroup.Gamma1_in_Gamma0 M) p hpM j hj Pl hPl
    obtain ⟨r₀, hr₀, hv₀Fin, hv₀Inf⟩ := h3d

    have hr₀' : ModularCurve.IsLaurentPlaceReduction Pl (IsLocalRing.residue ↥Pl) (ModularCurve.x1FunctionField M)
        (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) r₀ := hr₀

    obtain ⟨hL3, hL1, hL2raw⟩ :=
      AlgebraicCurve.CurveModel.existsUnique_point_and_ord_eq_and_ord_eq_zero_of_iso_pullback_of_ffEquiv_symm_germToFunctionField_eq
        ι M₀ Mk g hg ψ hsq

    let y₀ : Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) → {q : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ M₀.C // q ≫ M₀.toBase = 𝟙 _} := fun Q₀ => M₀.pointEquivPlace.symm Q₀
    have hy₀ : ∀ Q₀, M₀.pointEquivPlace (y₀ Q₀) = Q₀ := fun Q₀ => Equiv.apply_symm_apply _ _
    let yk : Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) → {q : Spec (CommRingCat.of k) ⟶ Mk.C // q ≫ Mk.toBase = 𝟙 _} := fun Q₀ => (hL3 (y₀ Q₀)).exists.choose
    have hbc_over : ∀ Q₀, (yk Q₀).1 ≫ (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) = Spec.map (CommRingCat.ofHom ι) ≫ (y₀ Q₀).1 :=
      fun Q₀ => (hL3 (y₀ Q₀)).exists.choose_spec
    have hyk_unique : ∀ (Q₀) (y : {q : Spec (CommRingCat.of k) ⟶ Mk.C // q ≫ Mk.toBase = 𝟙 _}), y.1 ≫ (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) = Spec.map (CommRingCat.ofHom ι) ≫ (y₀ Q₀).1 → y = yk Q₀ :=
      fun Q₀ y hy => (hL3 (y₀ Q₀)).unique hy (hbc_over Q₀)

    let bc : Place (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) → Place k ↥(ModularCurve.x1FunctionFieldC k M) := fun Q₀ => Mk.pointEquivPlace (yk Q₀)
    have hbc_def : ∀ Q₀, bc Q₀ = Mk.pointEquivPlace (yk Q₀) := fun _ => rfl
    have hbc_comap : ∀ Q₀, (bc Q₀).toValuationSubring.comap ψ = Q₀.toValuationSubring := fun Q₀ => by
      have h := (hL1 (y₀ Q₀) (yk Q₀) (hbc_over Q₀)).1
      rwa [hy₀] at h
    have hbc_ord : ∀ (Q₀) (f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)), (bc Q₀).ord (ψ f) = Q₀.ord f := fun Q₀ f => by
      have h := (hL1 (y₀ Q₀) (yk Q₀) (hbc_over Q₀)).2 f
      rwa [hy₀] at h
    have hbc_inj : Function.Injective bc := fun Q₀ Q₁ h =>
      Place.ext (by rw [← hbc_comap Q₀, ← hbc_comap Q₁, h])
    have hL2 : ∀ Q : Place k ↥(ModularCurve.x1FunctionFieldC k M), (∀ Q₀, Q ≠ bc Q₀) → ∀ f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M), f ≠ 0 → Q.ord (ψ f) = 0 := by
      intro Q hQ f hf
      refine hL2raw Q ?_ f hf
      intro y0 y hy
      have hy' : y.1 ≫ (g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) = Spec.map (CommRingCat.ofHom ι) ≫ (y₀ (M₀.pointEquivPlace y0)).1 := by
        have : y₀ (M₀.pointEquivPlace y0) = y0 := Equiv.symm_apply_apply _ _
        rw [this]; exact hy
      rw [hyk_unique _ y hy', ← hbc_def]
      exact hQ _

    let r : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) → Place k ↥(ModularCurve.x1FunctionFieldC k M) := fun P => bc (r₀ P)
    have hr_def : ∀ P, r P = bc (r₀ P) := fun _ => rfl
    have hr_comap : ∀ P, (r P).toValuationSubring.comap ψ = (r₀ P).toValuationSubring := fun P => hbc_comap (r₀ P)
    have hr_ord : ∀ (P) (f : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)), (r P).ord (ψ f) = (r₀ P).ord f := fun P f => hbc_ord (r₀ P) f

    have hcoeffπ : ∀ yq : LaurentSeries ↥Pl,
        ModularCurve.coeffMap πk yq = ModularCurve.coeffMap ι (ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yq) := by
      intro yq
      rw [ModularCurve.coeffMap_coeffMap, hιπ]
    have hψconst : ∀ c : IsLocalRing.ResidueField ↥Pl,
        ψ (algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) c) = algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (ι c) := by
      intro c
      apply Subtype.ext
      rw [hψ]
      have hC : ∀ {L : Type} [Field L] (d : L), HahnSeries.C d = algebraMap L (LaurentSeries L) d := by
        intro L _ d
        first
          | rfl
          | exact (HahnSeries.ofPowerSeries_C (Γ := ℤ) (R := L) d).symm
      have e1 : ((algebraMap (IsLocalRing.ResidueField ↥Pl) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M) c : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          HahnSeries.single 0 c := by
        simp
        rw [← hC, HahnSeries.C_apply]
      have e2 : ((algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (ι c) : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = HahnSeries.single 0 (ι c) := by
        simp
        rw [← hC, HahnSeries.C_apply]
      rw [e1, e2, ModularCurve.coeffMap_single]
    have hpush : ∀ (P) (x : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M)), x ∈ (r₀ P).toValuationSubring.nonunits →
        ψ x ∈ (r P).toValuationSubring.nonunits := by
      intro P x hx
      obtain ⟨hxmem, hxmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
      have hψx : ψ x ∈ (r P).toValuationSubring := by
        have : x ∈ (r P).toValuationSubring.comap ψ := by rw [hr_comap]; exact hxmem
        exact this
      rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      refine ⟨hψx, ?_⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxmax
      apply hxmax
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
      have hx0 : x ≠ 0 := by
        rintro rfl
        have h : ψ 0 * (w : ↥(ModularCurve.x1FunctionFieldC k M)) = 1 := congrArg Subtype.val hw
        rw [map_zero, zero_mul] at h
        exact zero_ne_one h

      have hwval : (w : ↥(ModularCurve.x1FunctionFieldC k M)) = (ψ x)⁻¹ := by
        have h : ψ x * (w : ↥(ModularCurve.x1FunctionFieldC k M)) = 1 := congrArg Subtype.val hw
        exact (eq_inv_of_mul_eq_one_right h)
      have hxinv : x⁻¹ ∈ (r₀ P).toValuationSubring := by
        rw [← hr_comap P]
        show ψ x⁻¹ ∈ (r P).toValuationSubring
        rw [map_inv₀, ← hwval]
        exact w.2
      exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hxinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
    have hadj : ModularCurve.x1FunctionFieldC k M =
        IntermediateField.adjoin k (ModularCurve.coeffMap ι '' (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M : Set (LaurentSeries (IsLocalRing.ResidueField ↥Pl)))) := by
      letI : Algebra (IsLocalRing.ResidueField ↥Pl) k := ι.toAlgebra
      exact ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) k
        (CongruenceSubgroup.Gamma1 M)
    have hdesc : ∀ z : LaurentSeries (IsLocalRing.ResidueField ↥Pl),
        ModularCurve.coeffMap ι z ∈ ModularCurve.x1FunctionFieldC k M → z ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M := by
      intro z hz
      apply ModularCurve.mem_of_coeffMap_mem_adjoin_image_of_ringHom ι
      rw [← hadj]
      exact hz
    have hr : ModularCurve.IsLaurentPlaceReduction Pl πk (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionFieldC k M) r := by
      haveI : AlgebraicCurve.IsCurveOver k ↥(ModularCurve.x1FunctionFieldC k M) :=
        ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed k (CongruenceSubgroup.Gamma1 M) hT
      refine ⟨fun P => ?_, ?_⟩
      ·
        rw [AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed (r P)]
        exact (ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ)
          (CongruenceSubgroup.Gamma1 M) hT (ModularCurve.x1FunctionField M) rfl P).symm
      · intro yq hyq hyqk hyq0 D hD Q

        have hyq0' : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yq ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField ↥Pl) M :=
          hdesc _ (by rw [← hcoeffπ]; exact hyqk)
        have hne0 : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yq ≠ 0 := by
          intro h
          apply hyq0
          rw [hcoeffπ, h, map_zero]
        have h2 := hr₀'.2 yq hyq hyq0' hne0 D hD
        have hψy : ψ ⟨_, hyq0'⟩ = ⟨ModularCurve.coeffMap πk yq, hyqk⟩ := Subtype.ext (by rw [hψ]; exact (hcoeffπ yq).symm)
        have hcomp : Finsupp.mapDomain r D = Finsupp.mapDomain bc (Finsupp.mapDomain r₀ D) := by
          rw [← Finsupp.mapDomain_comp]
          rfl
        rw [hcomp]
        by_cases hQ : ∃ Q₀, Q = bc Q₀
        · obtain ⟨Q₀, rfl⟩ := hQ
          rw [Finsupp.mapDomain_apply hbc_inj, h2 Q₀, ← hbc_ord Q₀, hψy]
        · push Not at hQ
          rw [Finsupp.mapDomain_notin_range _ _ (by rintro ⟨Q₀, rfl⟩; exact hQ Q₀ rfl), ← hψy,
            hL2 Q hQ _ (fun h => hne0 (congrArg Subtype.val h))]

    refine ⟨r, hr, ?_, ?_⟩
    · intro P β hP b yb bbar h1 h2
      have h0 := hv₀Fin P β hP b yb (M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) h1 (hread₀ b yb h1)
      have hψb : ψ (M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) = bbar := Subtype.ext (by
        rw [hψ, hread₀ b yb h1, h2]; exact (hcoeffπ yb).symm)
      have h3 := hpush P _ h0
      have hιπ' : ι (IsLocalRing.residue ↥Pl (β b)) = πk (β b) := by rw [← hιπ]; rfl
      rw [map_sub, hψb, hψconst, hιπ'] at h3
      exact h3
    · intro P β hP b yb bbar h1 h2
      have h0 := hv₀Inf P β hP b yb (M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) h1 (hread₀Inf b yb h1)
      have hψb : ψ (M₀.ffEquiv.symm
            (M₀.C.germToFunctionField ((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))) ⁻¹ᵁ ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤))
              (((e₀ ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥Pl).comp ρ₀)))).app ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) ''ᵁ ⊤)).hom
                (((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))).inv b))))) = bbar := Subtype.ext (by
        rw [hψ, hread₀Inf b yb h1, h2]; exact (hcoeffπ yb).symm)
      have h3 := hpush P _ h0
      have hιπ' : ι (IsLocalRing.residue ↥Pl (β b)) = πk (β b) := by rw [← hιπ]; rfl
      rw [map_sub, hψb, hψconst, hιπ'] at h3
      exact h3

  refine ⟨CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans, eη, hiso, heη, hcFin, hcInf, hgal, ρ₀, hρ₀, Mk, ek, hisoK, hek, πFin, πInf, hqFin, hqInf, hcenFin, hcenInf, r, hr, ?_⟩
  intro xA x y hx hy

  obtain ⟨P, hPx⟩ : ∃ P, (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace x = P :=
    ⟨_, rfl⟩
  rw [hPx]

  have hj0 : ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ≠ 0 := fun h =>
    (Fact.out : j ≠ 0) (by exact_mod_cast h)
  have hπj : (πInf (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) :
        ↥(ModularCurve.x1FunctionFieldC k M)) *
      πFin (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) = 1 := by
    obtain ⟨y₁, h₁, h₁'⟩ := hqInf (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)
    obtain ⟨y₂, h₂, h₂'⟩ := hqFin (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)
    have hprod : coeffMap Pl.subtype (y₁ * y₂) = 1 := by
      rw [map_mul, h₁, h₂, coe_jInvChartInf, coe_jChartFin, IntermediateField.coe_inv, map_inv₀,
        inv_mul_cancel₀ ((map_ne_zero _).mpr hj0)]
    have h12 : y₁ * y₂ = 1 :=
      coeffMap_injective (f := Pl.subtype) Subtype.val_injective (by rw [hprod, map_one])
    apply Subtype.ext
    rw [MulMemClass.coe_mul, OneMemClass.coe_one, h₁', h₂', ← map_mul, h12, map_one]
  have hπFin0 : (πFin (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) :
      ↥(ModularCurve.x1FunctionFieldC k M)) ≠ 0 := right_ne_zero_of_mul_eq_one hπj
  have hπInf0 : (πInf (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) :
      ↥(ModularCurve.x1FunctionFieldC k M)) ≠ 0 := left_ne_zero_of_mul_eq_one hπj
  have hπInf_eq : (πInf (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) :
      ↥(ModularCurve.x1FunctionFieldC k M)) =
      (πFin (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))⁻¹ :=
    eq_inv_of_mul_eq_one_left hπj
  have hπFin_eq : (πFin (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) :
      ↥(ModularCurve.x1FunctionFieldC k M)) =
      (πInf (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))⁻¹ :=
    eq_inv_of_mul_eq_one_right hπj

  have hpt : ∀ y' : {q : Spec (CommRingCat.of (k)) ⟶ (Mk).C //
        q ≫ (Mk).toBase = 𝟙 _},
      y'.1 ≫ ek ≫ pullback.fst _ _ = y.1 ≫ ek ≫ pullback.fst _ _ → y' = y := by
    intro y' h
    apply Subtype.ext
    rw [← cancel_mono (ek)]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h
    · simp only [Category.assoc, hek]
      rw [y'.2, y.2]

  have hκ0 : ∀ c : k, c ∈ maximalIdeal (k) → c = 0 := by
    intro c hc
    by_contra hne
    exact ((IsLocalRing.mem_maximalIdeal _).mp hc) (isUnit_iff_ne_zero.mpr hne)

  obtain ⟨y', hy'⟩ := (Mk).pointEquivPlace.surjective (r P)
  rw [← hy']

  rcases exists_chart_factorisation xA.1 with ⟨βA, hβA⟩ | ⟨βA, hβA⟩
  ·
    have hxc : x.1 ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Pl.subtype.comp βA)) ≫
          ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j := by
      rw [hx, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hP := hcFin x (Pl.subtype.comp βA) hxc
    rw [hPx] at hP
    have hyc : y.1 ≫ ek ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((πk).comp βA)) ≫
          ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j := by
      rw [hy, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hRP : ∀ b : ↥(chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
        (πFin b : ↥(ModularCurve.x1FunctionFieldC k M)) -
            algebraMap (k) ↥(ModularCurve.x1FunctionFieldC k M)
              (πk (βA b)) ∈ (r P).toValuationSubring.nonunits := by
      intro b
      obtain ⟨yb, h1, h2⟩ := hqFin b
      exact hvFinK P βA (fun b' => hP b') b yb (πFin b) h1 h2
    congr 1
    rcases exists_chart_factorisation_fin (y'.1 ≫ ek ≫ pullback.fst _ _) with
      ⟨β'', hβ''⟩ | ⟨β'', hβ'', hβ''j⟩
    ·
      have hQ' := hcenFin y' β'' hβ''
      rw [hy'] at hQ'
      have hββ : β'' = (πk).comp βA :=
        RingHom.ext fun b => const_eq_of_sub_mem_nonunits (r P) (hQ' b) (hRP b)
      exact (hpt y' (by rw [hβ'', hββ, ← hyc])).symm
    ·
      exfalso
      have hQ' := hcenInf y' β'' hβ'' (jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)
      rw [hy', hκ0 _ hβ''j, map_zero, sub_zero, hπInf_eq] at hQ'
      exact false_of_mem_of_inv_mem_nonunits hπFin0
        (mem_of_sub_algebraMap_mem_nonunits (r P) (hRP _)) hQ'
  ·
    have hxc : x.1 ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Pl.subtype.comp βA)) ≫
          ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j := by
      rw [hx, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hP := hcInf x (Pl.subtype.comp βA) hxc
    rw [hPx] at hP
    have hyc : y.1 ≫ ek ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom ((πk).comp βA)) ≫
          ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j := by
      rw [hy, hβA, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hRP : ∀ b : ↥(chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
        (πInf b : ↥(ModularCurve.x1FunctionFieldC k M)) -
            algebraMap (k) ↥(ModularCurve.x1FunctionFieldC k M)
              (πk (βA b)) ∈ (r P).toValuationSubring.nonunits := by
      intro b
      obtain ⟨yb, h1, h2⟩ := hqInf b
      exact hvInfK P βA (fun b' => hP b') b yb (πInf b) h1 h2
    congr 1
    rcases exists_chart_factorisation_inf (y'.1 ≫ ek ≫ pullback.fst _ _) with
      ⟨β'', hβ''⟩ | ⟨β'', hβ'', hβ''j⟩
    · have hQ' := hcenInf y' β'' hβ''
      rw [hy'] at hQ'
      have hββ : β'' = (πk).comp βA :=
        RingHom.ext fun b => const_eq_of_sub_mem_nonunits (r P) (hQ' b) (hRP b)
      exact (hpt y' (by rw [hβ'', hββ, ← hyc])).symm
    · exfalso
      have hQ' := hcenFin y' β'' hβ'' (jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)
      rw [hy', hκ0 _ hβ''j, map_zero, sub_zero, hπFin_eq] at hQ'
      exact false_of_mem_of_inv_mem_nonunits hπInf0
        (mem_of_sub_algebraMap_mem_nonunits (r P) (hRP _)) hQ'

end S_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom
end P2MW
export P2MW.S_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom (solution)
