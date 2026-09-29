-- Prove2me | solution 1 for ModularCurve.XOneP.isUnramifiedAt_chartAlgFin_of_not_isMaximal_twoChartIntegralModel_x1_mul_x1x0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1ba84316-03a4-53c0-b290-2b3202c3f093

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one
import Theorems.Thm_ModularCurve_exists_ord_eq_one_of_place_x1FunctionField_mul_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_XOneP_exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0
import Theorems.Thm_ModularCurve_XOneP_exists_eq_mul_of_mem_nonunits_valuationSubring_x1_mul
import Theorems.Thm_ModularCurve_relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0
import Theorems.Thm_Algebra_IsSeparable_of_coprime_finrank_expChar
import Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
import Theorems.Thm_Ideal_finrank_residueField_le_finrank_of_height_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_isUnramifiedAt_chartAlgFin_of_not_isMaximal_twoChartIntegralModel_x1_mul_x1x0
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~H1 AlgebraicCurve.TwoChartIntegralModel"

theorem UnramH1.horizontal
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) [Fact (j₁ ≠ 0)]
    (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
    (hιF : ∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L))
    [Algebra ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j)]
    (halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x = ιF x)
    [Module.Finite ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j)]
    [IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K] [IsFractionRing ↥(chartAlgFin A (↥K₁) j₁) ↥K₁]
    [IsNoetherianRing ↥(chartAlgFin A (↥K₁) j₁)]
    (hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal ↥(chartAlgFin A (↥K) j)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∉ Q) :
    Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K₁) j₁) Q := by

  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K {j}
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₁) j₁) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K₁ {j₁}
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq fun a => by rw [halg, ιF.commutes]
  let φ : ↥K₁ →ₐ[L] ↥K := IntermediateField.inclusion hle
  have hι : ∀ x : ↥(chartAlgFin A (↥K₁) j₁),
      algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x) =
        φ (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥K₁ x) := by
    intro x
    rw [halg]
    apply Subtype.ext
    show (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L)
    exact hιF x
  let jB : ↥(chartAlgFin A (↥K) j) := jChartFin A (↥K) j
  have hjB : algebraMap ↥(chartAlgFin A (↥K) j) ↥K jB = j := rfl
  have he : ∀ w : AlgebraicCurve.Place L ↥K, 0 ≤ w.ord (algebraMap ↥(chartAlgFin A (↥K) j) ↥K jB) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1 := by
    intro w hw
    rw [hjB] at hw
    obtain ⟨t, htK₁, ht1⟩ :=
      ModularCurve.exists_ord_eq_one_of_place_x1FunctionField_mul_of_ord_nonneg p M hM hpM L K hK K₁ hK₁ j hj w hw
    have hφt : φ ⟨(t : LaurentSeries L), htK₁⟩ = t := Subtype.ext rfl
    have h := AlgebraicCurve.Place.ord_restrictAlong φ hint w ⟨(t : LaurentSeries L), htK₁⟩
    rw [hφt, ht1] at h
    have h0 : (0 : ℤ) ≤ (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) := Int.natCast_nonneg _
    exact_mod_cast Int.eq_one_of_mul_eq_one_right h0 h.symm
  exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_forall_ramificationIndexAlong_eq_one L A ↥K ↥K₁ φ
    ↥(chartAlgFin A (↥K) j) ↥(chartAlgFin A (↥K₁) j₁) hι hint jB he ϖ hϖ Q hQ1 hϖQ

theorem UnramH1.maximalIdeal_eq_span_of_vertical
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    (F : Type u) [Field F] [Algebra A F] [Algebra L F] [IsScalarTower A L F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental A j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set F)) F)
    [IsNoetherianRing ↥(chartAlgFin A F j)] [IsFractionRing ↥(chartAlgFin A F j) F]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hram : ∀ V : ValuationSubring F,
      (∀ a : A, algebraMap A F a ∈ V) →
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A F a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ f : F, f ∈ V.nonunits → ∃ g : F, g ∈ V ∧ f = algebraMap A F ϖ * g)
    (Q : Ideal ↥(chartAlgFin A F j)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A ↥(chartAlgFin A F j) ϖ ∈ Q) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
      Ideal.span {algebraMap ↥(chartAlgFin A F j) (Localization.AtPrime Q) (algebraMap A ↥(chartAlgFin A F j) ϖ)} := by
  classical
  haveI : IsIntegrallyClosed ↥(chartAlgFin A F j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A F {j}

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖprime : Prime ϖ := hϖirr.prime
  have hAB : Function.Injective (algebraMap A ↥(chartAlgFin A F j)) := by
    intro a b h
    have h' := congrArg (algebraMap ↥(chartAlgFin A F j) F) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A L F, IsScalarTower.algebraMap_apply A L F] at h'
    exact IsFractionRing.injective A L ((algebraMap L F).injective h')
  have hϖB0 : algebraMap A ↥(chartAlgFin A F j) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hAB]
    exact hϖprime.ne_zero
  have hQ0 : Q ≠ ⊥ := fun h => hϖB0 (by simpa [h] using hϖQ)

  have hQmin : Q ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A F j) ϖ}).minimalPrimes := by
    refine ⟨⟨‹Q.IsPrime›, (Ideal.span_singleton_le_iff_mem _).mpr hϖQ⟩, ?_⟩
    rintro P ⟨hP, hϖP⟩ hPQ

    by_contra hne
    have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hne (h ▸ le_rfl))
    haveI := hP
    have hP0 : P ≠ ⊥ := fun h => hϖB0 (by
      have := (Ideal.span_singleton_le_iff_mem _).mp hϖP
      simpa [h] using this)
    have hPne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
      exact hP0
    have h1 : Q.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hQ1]; exact_mod_cast le_rfl
    have hlt' := (Ideal.height_le_iff.mp h1) P hP hlt
    exact hPne (ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast hlt'))

  obtain ⟨V, hVdvr, hBV, hcentre, hϖV, hVj⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin A L F j htj hFD hsep
      ϖ hϖprime Q hQmin

  have hVA : ∀ a : A, algebraMap A F a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply A ↥(chartAlgFin A F j) F]
    exact hBV _
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A F a ∈ V.nonunits := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, ValuationSubring.mem_nonunits_iff, Valuation.map_mul]
    have h1 : V.valuation (algebraMap A F ϖ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hϖV
    have h2 : V.valuation (algebraMap A F c) ≤ 1 := V.valuation_le_one ⟨_, hVA c⟩
    calc V.valuation (algebraMap A F ϖ) * V.valuation (algebraMap A F c)
        ≤ V.valuation (algebraMap A F ϖ) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rwa [mul_one]
  have hVj' : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
    intro P hP
    refine hVj P fun hdvd => hP ?_
    obtain ⟨R, rfl⟩ := hdvd
    rw [Polynomial.map_mul, Polynomial.map_C]
    have : IsLocalRing.residue A ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr (by
      rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
    rw [this, Polynomial.C_0, zero_mul]
  have key := hram V hVA hVm hVj'

  have hnf : ¬ IsField (Localization.AtPrime Q) := IsLocalization.AtPrime.not_isField ↥(chartAlgFin A F j) hQ0 (Localization.AtPrime Q)
  haveI : IsIntegrallyClosed (Localization.AtPrime Q) := isIntegrallyClosed_of_isLocalization (Localization.AtPrime Q) Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have huniq : ∃! P : Ideal (Localization.AtPrime Q), P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal (Localization.AtPrime Q), ⟨?_, inferInstance⟩, ?_⟩
    · intro h
      exact hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    · rintro P' ⟨hP'0, hP'p⟩
      haveI := hP'p

      let P₀ : Ideal ↥(chartAlgFin A F j) := P'.comap (algebraMap ↥(chartAlgFin A F j) (Localization.AtPrime Q))
      have hP₀Q : P₀ ≤ Q := by
        intro b hb
        by_contra hbQ
        have hu : IsUnit (algebraMap ↥(chartAlgFin A F j) (Localization.AtPrime Q) b) := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q b).mpr hbQ
        exact hP'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hb hu)
      have hP₀0 : P₀ ≠ ⊥ := by
        intro h0
        apply hP'0
        have := IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) P'
        rw [show Ideal.under ↥(chartAlgFin A F j) P' = P₀ from rfl, h0, Ideal.map_bot] at this
        exact this.symm
      have hP₀eq : P₀ = Q := by
        by_contra hne
        have hlt : P₀ < Q := lt_of_le_of_ne hP₀Q hne
        have hPne : P₀.height ≠ 0 := by
          rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
          exact hP₀0
        have h1 : Q.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hQ1]; exact_mod_cast le_rfl
        have hlt' := (Ideal.height_le_iff.mp h1) P₀ inferInstance hlt
        exact hPne (ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast hlt'))
      have := IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) P'
      rw [show Ideal.under ↥(chartAlgFin A F j) P' = P₀ from rfl, hP₀eq] at this
      rw [← this, Localization.AtPrime.map_eq_maximalIdeal]
  have h03 := (IsDiscreteValuationRing.TFAE (Localization.AtPrime Q) hnf).out 0 3
  haveI hdvrS : IsDiscreteValuationRing (Localization.AtPrime Q) := h03.mpr ⟨inferInstance, huniq⟩

  have hunits : ∀ y : Q.primeCompl, IsUnit (algebraMap ↥(chartAlgFin A F j) F y) := fun y =>
    isUnit_iff_ne_zero.mpr (by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ↥(chartAlgFin A F j) F)]
      exact fun h => y.2 (h ▸ Q.zero_mem))
  letI algSF : Algebra (Localization.AtPrime Q) F := (IsLocalization.lift (M := Q.primeCompl) (S := Localization.AtPrime Q) hunits).toAlgebra
  haveI : IsScalarTower ↥(chartAlgFin A F j) (Localization.AtPrime Q) F :=
    IsScalarTower.of_algebraMap_eq fun b => (IsLocalization.lift_eq (M := Q.primeCompl) (S := Localization.AtPrime Q) hunits b).symm
  haveI : IsFractionRing (Localization.AtPrime Q) F := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl (Localization.AtPrime Q) F
  have hSFinj : Function.Injective (algebraMap (Localization.AtPrime Q) F) := IsFractionRing.injective (Localization.AtPrime Q) F

  have hcentre' : ∀ s : (Localization.AtPrime Q), s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) → algebraMap (Localization.AtPrime Q) F s ∈ V.nonunits := by
    intro s hs
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl s
    have hb : b ∈ Q := (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime Q) Q b t).mp hs
    have hbV : algebraMap ↥(chartAlgFin A F j) F b ∈ V.nonunits := (hcentre b).mp hb
    have htV : (algebraMap ↥(chartAlgFin A F j) F t)⁻¹ ∈ V := by
      rcases V.mem_or_inv_mem (algebraMap ↥(chartAlgFin A F j) F t)⁻¹ with h | h
      · exact h
      · rw [inv_inv] at h

        have htu : algebraMap ↥(chartAlgFin A F j) F t ∉ V.nonunits := fun h' => t.2 ((hcentre t).mpr h')
        rw [ValuationSubring.mem_nonunits_iff, not_lt] at htu
        have hle : V.valuation (algebraMap ↥(chartAlgFin A F j) F t) ≤ 1 := V.valuation_le_one ⟨_, hBV t⟩
        have heq : V.valuation (algebraMap ↥(chartAlgFin A F j) F t) = 1 := le_antisymm hle htu
        have : V.valuation (algebraMap ↥(chartAlgFin A F j) F t)⁻¹ ≤ 1 := by rw [map_inv₀, heq, inv_one]
        exact (V.valuation_le_one_iff _).mp this
    have hmk : algebraMap (Localization.AtPrime Q) F (IsLocalization.mk' (Localization.AtPrime Q) b t) = algebraMap ↥(chartAlgFin A F j) F b * (algebraMap ↥(chartAlgFin A F j) F t)⁻¹ := by
      rw [show algebraMap (Localization.AtPrime Q) F = IsLocalization.lift (M := Q.primeCompl) (S := Localization.AtPrime Q) hunits from rfl,
        IsLocalization.lift_mk'_spec]
      have hne0 := (hunits t).ne_zero
      field_simp
    rw [hmk, ValuationSubring.mem_nonunits_iff, Valuation.map_mul]
    have h1 := (ValuationSubring.mem_nonunits_iff _).mp hbV
    have h2 : V.valuation (algebraMap ↥(chartAlgFin A F j) F t)⁻¹ ≤ 1 := V.valuation_le_one ⟨_, htV⟩
    calc V.valuation (algebraMap ↥(chartAlgFin A F j) F b) * V.valuation (algebraMap ↥(chartAlgFin A F j) F t)⁻¹
        ≤ V.valuation (algebraMap ↥(chartAlgFin A F j) F b) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rwa [mul_one]
  have hfill : ∀ x : F, x ∈ V → ∃ s : (Localization.AtPrime Q), algebraMap (Localization.AtPrime Q) F s = x := by
    intro x hx
    rcases ValuationRing.isInteger_or_isInteger (Localization.AtPrime Q) x with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨s, hs⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [map_zero, hx0]⟩
      by_cases hsu : IsUnit s
      · obtain ⟨u, rfl⟩ := hsu
        refine ⟨↑u⁻¹, ?_⟩
        have : algebraMap (Localization.AtPrime Q) F ↑u * x = 1 := by rw [hs, inv_mul_cancel₀ hx0]
        calc algebraMap (Localization.AtPrime Q) F ↑u⁻¹ = algebraMap (Localization.AtPrime Q) F ↑u⁻¹ * (algebraMap (Localization.AtPrime Q) F ↑u * x) := by rw [this, mul_one]
          _ = x := by rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      · exfalso
        have hsm : s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := (IsLocalRing.mem_maximalIdeal s).mpr hsu
        have hxinv : x⁻¹ ∈ V.nonunits := hs ▸ hcentre' s hsm
        rw [ValuationSubring.mem_nonunits_iff, map_inv₀] at hxinv
        have hxle : V.valuation x ≤ 1 := V.valuation_le_one ⟨x, hx⟩
        have hx0' : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
        have : (1 : _) < V.valuation x := by
          have := hxinv
          rwa [inv_lt_one₀ (zero_lt_iff.mpr hx0')] at this
        exact absurd hxle (not_le.mpr this)

  apply le_antisymm
  · intro s hs
    obtain ⟨g, hgV, hg⟩ := key _ (hcentre' s hs)
    obtain ⟨t, rfl⟩ := hfill g hgV
    have : algebraMap (Localization.AtPrime Q) F s = algebraMap (Localization.AtPrime Q) F (algebraMap ↥(chartAlgFin A F j) (Localization.AtPrime Q) (algebraMap A ↥(chartAlgFin A F j) ϖ) * t) := by
      rw [hg, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply A L F]
    rw [hSFinj this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hϖQ

theorem UnramH1.ringKrullDim_chartAlgFin_le_two
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] (j : F) [Fact (j ≠ 0)] (htj : Transcendental A j) :
    ringKrullDim ↥(chartAlgFin A F j) ≤ 2 := by
  classical
  let R' : Subalgebra A F := Algebra.adjoin A ({j} : Set F)
  have hle : R' ≤ chartAlgFin A F j := adjoin_le_chartAlg A F {j}
  letI : Algebra ↥R' ↥(chartAlgFin A F j) := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥R' ↥(chartAlgFin A F j) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral ↥R' ↥(chartAlgFin A F j) := ⟨fun b =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥R' ↥(chartAlgFin A F j) F) Subtype.val_injective).mp b.2⟩

  have h1 : ringKrullDim ↥(chartAlgFin A F j) ≤ ringKrullDim ↥R' := by
    refine Order.krullDim_le_of_strictMono
      (fun P : PrimeSpectrum ↥(chartAlgFin A F j) => PrimeSpectrum.comap (algebraMap ↥R' ↥(chartAlgFin A F j)) P) ?_
    intro P Q hPQ
    have hPQ' : P.asIdeal < Q.asIdeal := hPQ
    show (PrimeSpectrum.comap _ P).asIdeal < (PrimeSpectrum.comap _ Q).asIdeal
    exact Ideal.IsIntegral.comap_lt_comap hPQ'

  have hinj : Function.Injective (Polynomial.aeval (R := A) j) := transcendental_iff_injective.mp htj
  have e : Polynomial A ≃ₐ[A] ↥R' :=
    (AlgEquiv.ofInjective (Polynomial.aeval j) hinj).trans
      (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval A j).symm)
  have h2 : ringKrullDim ↥R' = ringKrullDim (Polynomial A) := (RingEquiv.ringKrullDim e.toRingEquiv).symm
  rw [h2, Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one A] at h1
  exact h1.trans (by norm_num)

theorem UnramH1.generic_point
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L)) (K₁ : IntermediateField L (LaurentSeries L)) (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [Algebra A ↥K] [Algebra A ↥K₁]
    (j : ↥K) [Fact (j ≠ 0)] (j₁ : ↥K₁) [Fact (j₁ ≠ 0)]
    (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
    (hιF : ∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L))
    [Algebra ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j)]
    (halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x = ιF x)
    [IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K] [IsFractionRing ↥(chartAlgFin A (↥K₁) j₁) ↥K₁]
    (hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral) :
    Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K₁) j₁) (⊥ : Ideal ↥(chartAlgFin A (↥K) j)) := by
  classical

  letI algK : Algebra ↥K₁ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI algBK : Algebra ↥(chartAlgFin A (↥K₁) j₁) ↥K := ((algebraMap ↥K₁ ↥K).comp (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥K₁)).toAlgebra
  haveI : @IsScalarTower ↥(chartAlgFin A (↥K₁) j₁) ↥K₁ ↥K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomm : ∀ x, algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥K x = algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x) := by
    intro x
    rw [halg]
    apply Subtype.ext
    exact (hιF x).symm
  haveI : Algebra.IsIntegral ↥K₁ ↥K := ⟨hint⟩
  haveI : Algebra.IsSeparable ↥K₁ ↥K := Algebra.IsSeparable.of_integral ↥K₁ ↥K
  haveI h1 : Algebra.FormallyUnramified ↥(chartAlgFin A (↥K₁) j₁) ↥K₁ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ↥(chartAlgFin A (↥K₁) j₁))
  haveI h2 : Algebra.FormallyUnramified ↥K₁ ↥K := Algebra.FormallyUnramified.of_isSeparable ↥K₁ ↥K
  haveI h3 : Algebra.FormallyUnramified ↥(chartAlgFin A (↥K₁) j₁) ↥K := Algebra.FormallyUnramified.comp ↥(chartAlgFin A (↥K₁) j₁) ↥K₁ ↥K

  haveI : IsLocalization ((⊥ : Ideal ↥(chartAlgFin A (↥K) j)).primeCompl) ↥K := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  let e0 : ↥K ≃ₐ[↥(chartAlgFin A (↥K) j)] Localization.AtPrime (⊥ : Ideal ↥(chartAlgFin A (↥K) j)) :=
    IsLocalization.algEquiv ((⊥ : Ideal ↥(chartAlgFin A (↥K) j)).primeCompl) ↥K _
  let e : ↥K ≃ₐ[↥(chartAlgFin A (↥K₁) j₁)] Localization.AtPrime (⊥ : Ideal ↥(chartAlgFin A (↥K) j)) :=
    AlgEquiv.ofRingEquiv (f := e0.toRingEquiv) fun x => by
      show e0 (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥K x) = algebraMap ↥(chartAlgFin A (↥K₁) j₁) (Localization.AtPrime (⊥ : Ideal ↥(chartAlgFin A (↥K) j))) x
      rw [hcomm, AlgEquiv.commutes]
      rfl
  show Algebra.FormallyUnramified ↥(chartAlgFin A (↥K₁) j₁) (Localization.AtPrime (⊥ : Ideal ↥(chartAlgFin A (↥K) j)))
  exact Algebra.FormallyUnramified.of_equiv e

theorem UnramH1.isIntegral_inclusion
    (L : Type) [Field L]
    (K : IntermediateField L (LaurentSeries L)) (K₁ : IntermediateField L (LaurentSeries L)) (hle : K₁ ≤ K)
    (j : ↥K) (hjK₁ : ((j : LaurentSeries L)) ∈ K₁)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical
  haveI := hFD
  set E := IntermediateField.adjoin L ({j} : Set ↥K) with hE

  have hEK₁ : ∀ x : ↥E, (((x : ↥K) : LaurentSeries L)) ∈ K₁ := by
    have hle' : E ≤ IntermediateField.comap K.val K₁ := by
      rw [hE, IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hjK₁
    intro x
    exact hle' x.2
  let ψ : ↥E →+* ↥K₁ :=
    { toFun := fun x => ⟨((x : ↥K) : LaurentSeries L), hEK₁ x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hψ : (IntermediateField.inclusion hle).toRingHom.comp ψ = algebraMap ↥E ↥K := by
    ext x
    rfl
  intro y
  have hy : IsIntegral ↥E y := Algebra.IsIntegral.isIntegral y
  refine ⟨(minpoly ↥E y).map ψ, (minpoly.monic hy).map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hψ, ← Polynomial.aeval_def, minpoly.aeval]

set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))

    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (hle : K₁ ≤ K)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ιF : ↥(chartAlgFin A (↥K₁) j₁) →ₐ[A] ↥(chartAlgFin A (↥K) j))
    (hιF : ∀ x, (((ιF x : ↥K) : LaurentSeries L)) = ((x : ↥K₁) : LaurentSeries L)) :
    letI : Algebra ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) := ιF.toRingHom.toAlgebra
    ∀ (Q : Ideal ↥(chartAlgFin A (↥K) j)) [Q.IsPrime], ¬ Q.IsMaximal →
      Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K₁) j₁) Q := by

  classical
  intro Q _ hQmax
  letI instAlg : Algebra ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) := ιF.toRingHom.toAlgebra
  have halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x = ιF x := fun _ => rfl

  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htj₁ : Transcendental A j₁ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₁ A j₁ hj₁
  have hT1 : ∀ N : ℕ, ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := fun N => by
    rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]
  have hT0 : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 p := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) (hT1 _) L K hK j hj
  have hFD₁ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₁} : Set ↥K₁)) ↥K₁ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ⟨hT1 _, hT0⟩ L K₁ hK₁ j₁ hj₁
  haveI := hFD
  haveI := hFD₁
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := inferInstance
  have hsep₁ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₁} : Set ↥K₁)) ↥K₁ := inferInstance
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K) j) := by
    haveI := (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L ↥K j htj hFD hsep).1
    exact Algebra.FiniteType.isNoetherianRing A ↥(chartAlgFin A (↥K) j)
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₁) j₁) := by
    haveI := (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L ↥K₁ j₁ htj₁ hFD₁ hsep₁).1
    exact Algebra.FiniteType.isNoetherianRing A ↥(chartAlgFin A (↥K₁) j₁)
  haveI : IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L ↥K {j}
  haveI : IsFractionRing ↥(chartAlgFin A (↥K₁) j₁) ↥K₁ := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L ↥K₁ {j₁}
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K {j}
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₁) j₁) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K₁ {j₁}
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) := IsScalarTower.of_algebraMap_eq fun a => by rw [halg, ιF.commutes]

  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : A, IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    ⟨_, (IsLocalRing.maximalIdeal A).span_singleton_generator.symm⟩

  obtain ⟨m, ιF', ιI', hιF', -, -, -, -, -, -, -, -, hfinF, -, -, -⟩ :=
    ModularCurve.XOneP.exists_floorHom_isFinite_twoChartIntegralModel_x1_mul_x1x0 p M hM hpM L ζ hζ K hK K₁ hK₁ hle
      A hAp hζA j hj j₁ hj₁ ϖ hϖ
  have hιeq : ιF' = ιF := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (hιF' x).trans (hιF x).symm
  haveI hfinB : Module.Finite ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) := by
    have h := hfinF
    rw [hιeq] at h
    exact h

  have hjK₁ : ((j : LaurentSeries L)) ∈ K₁ := by rw [hj, ← hj₁]; exact j₁.2
  have hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral := UnramH1.isIntegral_inclusion L K K₁ hle j hjK₁ hFD

  by_cases hQ0 : Q = ⊥
  · subst hQ0
    exact UnramH1.generic_point L K K₁ hle A j j₁ ιF hιF halg hint

  have hQ1 : Q.height = 1 :=
    Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
      (UnramH1.ringKrullDim_chartAlgFin_le_two A ↥K j htj) Q hQ0 hQmax
  by_cases hϖQ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ Q
  ·

    letI locAlg : Algebra (Localization.AtPrime (Q.under ↥(chartAlgFin A (↥K₁) j₁))) (Localization.AtPrime Q) :=
      (Localization.localRingHom (Q.under ↥(chartAlgFin A (↥K₁) j₁)) Q (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j)) Ideal.LiesOver.over).toAlgebra
    haveI : Localization.AtPrime.IsLiesOverAlgebra (Q.under ↥(chartAlgFin A (↥K₁) j₁)) Q := ⟨rfl⟩

    have hram := ModularCurve.XOneP.exists_eq_mul_of_mem_nonunits_valuationSubring_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA
      j hj ϖ hϖ
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
        Ideal.span {algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime Q) (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ)} :=
      UnramH1.maximalIdeal_eq_span_of_vertical A L ↥K j htj hFD hsep ϖ hϖ hram Q hQ1 hϖQ
    have hϖq₀ : algebraMap A ↥(chartAlgFin A (↥K₁) j₁) ϖ ∈ Q.under ↥(chartAlgFin A (↥K₁) j₁) := by
      rw [Ideal.under_def, Ideal.mem_comap, halg, ιF.commutes]
      exact hϖQ
    have hmap : Ideal.map (algebraMap ↥(chartAlgFin A (↥K₁) j₁) (Localization.AtPrime Q)) (Q.under ↥(chartAlgFin A (↥K₁) j₁)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        have hx' : algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x ∈ Q := by
          rw [Ideal.under_def, Ideal.mem_comap] at hx
          exact hx
        rw [Ideal.mem_comap]
        show algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime Q) (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) x) ∈ _
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hx'
      · rw [hmax, Ideal.span_singleton_le_iff_mem]
        have heq : algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime Q) (algebraMap A ↥(chartAlgFin A (↥K) j) ϖ) =
            algebraMap ↥(chartAlgFin A (↥K₁) j₁) (Localization.AtPrime Q) (algebraMap A ↥(chartAlgFin A (↥K₁) j₁) ϖ) := by
          show _ = algebraMap ↥(chartAlgFin A (↥K) j) (Localization.AtPrime Q) (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) (algebraMap A ↥(chartAlgFin A (↥K₁) j₁) ϖ))
          rw [halg, ιF.commutes]
        rw [heq]
        exact Ideal.mem_map_of_mem _ hϖq₀

    letI algK : Algebra ↥K₁ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    letI algBK : Algebra ↥(chartAlgFin A (↥K₁) j₁) ↥K := ((algebraMap ↥K₁ ↥K).comp (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥K₁)).toAlgebra
    haveI : @IsScalarTower ↥(chartAlgFin A (↥K₁) j₁) ↥K₁ ↥K Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : @IsScalarTower ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) ↥K Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      rw [halg]
      apply Subtype.ext
      exact (hιF x).symm
    obtain ⟨hdeg, -, -⟩ :=
      ModularCurve.relfinrank_eq_sub_one_and_isGalois_and_isCyclic_x1FunctionField_mul_x1x0 p M hM hpM L K hK K₁ hK₁ hle
    rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hdeg
    have hdeg' : Module.finrank ↥K₁ ↥K = p - 1 := hdeg
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    haveI : FiniteDimensional ↥K₁ ↥K := Module.finite_of_finrank_pos (by rw [hdeg']; omega)
    haveI : Algebra.IsIntegral ↥K₁ ↥K := ⟨hint⟩
    haveI : Algebra.IsSeparable ↥K₁ ↥K := Algebra.IsSeparable.of_integral ↥K₁ ↥K
    have hinjF : Function.Injective (algebraMap ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j)) := by
      intro x y hxy
      rw [halg, halg] at hxy
      apply Subtype.ext
      apply Subtype.ext
      rw [← hιF x, ← hιF y, hxy]
    haveI : NoZeroSMulDivisors ↥(chartAlgFin A (↥K₁) j₁) ↥(chartAlgFin A (↥K) j) := ⟨fun {c x} h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun hc => hinjF (by rw [map_zero]; exact hc)⟩
    obtain ⟨hfinres, hle_res⟩ :=
      Ideal.finrank_residueField_le_finrank_of_height_eq_one (O := ↥(chartAlgFin A (↥K₁) j₁)) (C := ↥(chartAlgFin A (↥K) j)) ↥K₁ ↥K Q hQ1
    haveI := hfinres

    have hpq₀ : ((p : ℕ) : (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField) = 0 := by
      have hpA : (p : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAp
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpA
      have : (p : ↥(chartAlgFin A (↥K₁) j₁)) ∈ Q.under ↥(chartAlgFin A (↥K₁) j₁) := by
        have : (p : ↥(chartAlgFin A (↥K₁) j₁)) = algebraMap A ↥(chartAlgFin A (↥K₁) j₁) c * algebraMap A ↥(chartAlgFin A (↥K₁) j₁) ϖ := by
          rw [← map_mul, hc, map_natCast]
        rw [this]
        exact Ideal.mul_mem_left _ _ hϖq₀
      rw [← map_natCast (algebraMap ↥(chartAlgFin A (↥K₁) j₁) (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField), Ideal.algebraMap_residueField_eq_zero]
      exact this
    haveI : CharP (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpq₀
    haveI : ExpChar (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField p := ExpChar.prime (Fact.out : p.Prime)
    have hpos : 0 < Module.finrank (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField Q.ResidueField := Module.finrank_pos
    have hlt : Module.finrank (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField Q.ResidueField < p := by
      rw [hdeg'] at hle_res
      omega
    have hcop : Nat.Coprime (Module.finrank (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField Q.ResidueField) p :=
      (Nat.coprime_of_lt_prime hpos.ne' hlt (Fact.out : p.Prime)).symm
    have hsepres : Algebra.IsSeparable (Q.under ↥(chartAlgFin A (↥K₁) j₁)).ResidueField Q.ResidueField :=
      Algebra.IsSeparable.of_coprime_finrank_expChar _ _ p hcop
    exact (Algebra.isUnramifiedAt_iff_map_eq ↥(chartAlgFin A (↥K₁) j₁) (Q.under ↥(chartAlgFin A (↥K₁) j₁)) Q).mpr ⟨hsepres, hmap⟩
  ·
    exact UnramH1.horizontal p M hM hpM L K hK K₁ hK₁ hle A j hj j₁ ιF hιF halg hint ϖ hϖ Q hQ1 hϖQ

end S_ModularCurve_XOneP_isUnramifiedAt_chartAlgFin_of_not_isMaximal_twoChartIntegralModel_x1_mul_x1x0
end P2MW
export P2MW.S_ModularCurve_XOneP_isUnramifiedAt_chartAlgFin_of_not_isMaximal_twoChartIntegralModel_x1_mul_x1x0 (solution)
