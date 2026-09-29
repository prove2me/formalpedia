-- Prove2me | solution 1 for ModularCurve.XOneGammaZeroP.isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b93da0d9-bdf0-5031-b340-c195db7f48a9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
import Theorems.Thm_ModularCurve_exists_ord_eq_one_of_place_x1x0FunctionFieldC_gamma0_of_ord_nonneg_of_tame
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_eq_mul_of_mem_nonunits_valuationSubring_x1x0
import Theorems.Thm_ModularCurve_XOneGammaZeroP_finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
import Theorems.Thm_Ideal_height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneGammaZeroP_isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10"
p2m_attr_erase "simp" "CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add"
p2m_attr_erase "simp" "KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply"
p2m_attr_erase "simp" "ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve~H1 AlgebraicCurve.TwoChartIntegralModel"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem E9.ringKrullDim_chartAlgFin_le_two
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

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem E9.generic_point
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

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem E9.isIntegral_inclusion
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

theorem E9.exists_ringEquiv_pair {P Q R T : CommRingCat} (φ : P ⟶ Q) (eX : Q ≅ R) (eY : P ≅ T) (L : ↑T →+* ↑R)
    (h : eY.hom ≫ CommRingCat.ofHom L = φ ≫ eX.hom) :
    ∃ (eXr : ↑Q ≃+* ↑R) (eYr : ↑P ≃+* ↑T), (∀ x, eXr x = eX.hom.hom x) ∧ (∀ x, eYr x = eY.hom.hom x) ∧
      ∀ x, eXr (φ.hom x) = L (eYr x) := by
  refine ⟨eX.commRingCatIsoToRingEquiv, eY.commRingCatIsoToRingEquiv, fun _ => rfl, fun _ => rfl, fun x => ?_⟩
  have h' := congrArg (fun f => f.hom x) h
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h'
  exact h'.symm

theorem E9.algebraMap_mem_of_mem_maximalIdeal {A B S : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing S] [IsLocalRing S]
    (y : Ideal B) [y.IsPrime] (e : S ≃+* Localization.AtPrime y) (s : S) (hs : s ∈ IsLocalRing.maximalIdeal S)
    (a : A) (h : e s = algebraMap A (Localization.AtPrime y) a) : algebraMap A B a ∈ y := by
  have h2 : e s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu => hs (by simpa using hu.map e.symm)
  rw [h, IsScalarTower.algebraMap_apply A B (Localization.AtPrime y),
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y) y] at h2
  exact h2

namespace E9

theorem mod_ne_one_of_prime_lt_five (p : ℕ) (hp : p.Prime) (h5 : p < 5) : p % 3 ≠ 1 ∧ p % 4 ≠ 1 := by
  interval_cases p <;> simp_all <;> norm_num at hp

theorem deuring_of_ssToken (p : ℕ) [hp : Fact p.Prime]
    {A : Type u} [CommRing A] {F : Type u} [Field F] [Algebra A F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin A F j))
    (hpy : (algebraMap A ↥(chartAlgFin A F j) p) ∈ y.asIdeal)
    (hss : ∀ (Ω : Type u) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ : ↥(chartAlgFin A F j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A F j) ∈ ModularCurve.ssJSet p Ω)
    (Q : Ideal ↥(chartAlgFin A F j)) (hQy : Q ≤ y.asIdeal) :
    (jChartFin A F j ∈ Q → p % 3 ≠ 1) ∧ (jChartFin A F j - 1728 ∈ Q → p % 4 ≠ 1) := by
  classical
  haveI : y.asIdeal.IsPrime := y.isPrime
  let Ω := AlgebraicClosure (FractionRing (↥(chartAlgFin A F j) ⧸ y.asIdeal))
  let φ : ↥(chartAlgFin A F j) →+* Ω :=
    (algebraMap (FractionRing (↥(chartAlgFin A F j) ⧸ y.asIdeal)) Ω).comp
      ((algebraMap (↥(chartAlgFin A F j) ⧸ y.asIdeal) (FractionRing (↥(chartAlgFin A F j) ⧸ y.asIdeal))).comp
        (Ideal.Quotient.mk y.asIdeal))
  have hker : RingHom.ker φ = y.asIdeal := by
    ext b
    rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap (FractionRing (↥(chartAlgFin A F j) ⧸ y.asIdeal)) Ω).injective,
      map_eq_zero_iff _ (IsFractionRing.injective (↥(chartAlgFin A F j) ⧸ y.asIdeal) (FractionRing (↥(chartAlgFin A F j) ⧸ y.asIdeal))),
      Ideal.Quotient.eq_zero_iff_mem]
  have hpΩ : ((p : ℕ) : Ω) = 0 := by
    rw [← map_natCast φ p, ← RingHom.mem_ker, hker, ← map_natCast (algebraMap A ↥(chartAlgFin A F j)) p]
    exact hpy
  haveI : CharP Ω p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpΩ)
  have htok := hss Ω φ hker
  by_cases h5 : p < 5
  · exact ⟨fun _ => (mod_ne_one_of_prime_lt_five p hp.out h5).1, fun _ => (mod_ne_one_of_prime_lt_five p hp.out h5).2⟩
  have hp5 : 5 ≤ p := not_lt.mp h5
  refine ⟨fun hJ => ?_, fun hJ => ?_⟩
  · have h0 : φ (jChartFin A F j) = 0 := by rw [← RingHom.mem_ker, hker]; exact hQy hJ
    rw [h0] at htok
    have := (ModularCurve.zero_mem_ssJSet_iff p hp5 Ω).mp htok
    omega
  · have h0 : φ (jChartFin A F j - 1728) = 0 := by rw [← RingHom.mem_ker, hker]; exact hQy hJ
    rw [map_sub, sub_eq_zero] at h0
    have h1728 : φ (jChartFin A F j) = 1728 := by rw [h0, map_ofNat]
    rw [h1728] at htok
    have := (ModularCurve.ofNat1728_mem_ssJSet_iff p hp5 Ω).mp htok
    omega

end E9

theorem E9.isUnramifiedAt_stalk_of_chart {B₁ B : Type*} [CommRing B₁] [CommRing B]
    (ι : B₁ →+* B) (y : Ideal B) [y.IsPrime]
    (hunr : letI := ι.toAlgebra; ∀ (Q : Ideal B) [Q.IsPrime], Q ≤ y → ¬ Q.IsMaximal → Algebra.IsUnramifiedAt B₁ Q)
    {Sf S : Type*} [CommRing Sf] [CommRing S] [IsLocalRing S]
    (φ : Sf →+* S) (eX : S ≃+* Localization.AtPrime y) (eY : Sf ≃+* Localization.AtPrime (y.comap ι))
    (hdict : ∀ x, eX (φ x) = Localization.localRingHom (y.comap ι) y ι rfl (eY x)) :
    letI := φ.toAlgebra
    ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt Sf 𝔮 := by
  letI := ι.toAlgebra
  letI := φ.toAlgebra
  intro 𝔮 _ h𝔮
  letI algBS : Algebra B S := (eX.symm.toRingHom.comp (algebraMap B (Localization.AtPrime y))).toAlgebra
  letI algB₁Sf : Algebra B₁ Sf := (eY.symm.toRingHom.comp (algebraMap B₁ (Localization.AtPrime (y.comap ι)))).toAlgebra
  letI algB₁S : Algebra B₁ S := ((algebraMap Sf S).comp (algebraMap B₁ Sf)).toAlgebra
  haveI : IsScalarTower B₁ Sf S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hcomm : ∀ r : B₁, φ (eY.symm (algebraMap B₁ _ r)) = eX.symm (algebraMap B _ (ι r)) := by
    intro r
    apply eX.injective
    rw [hdict, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, Localization.localRingHom_to_map]
  haveI : IsScalarTower B₁ B S := IsScalarTower.of_algebraMap_eq (fun r => hcomm r)
  haveI : IsLocalization.AtPrime S y :=
    IsLocalization.isLocalization_of_algEquiv y.primeCompl
      (AlgEquiv.ofRingEquiv (f := eX.symm) (fun _ => rfl) : Localization.AtPrime y ≃ₐ[B] S)

  haveI : IsScalarTower B₁ Sf (Localization.AtPrime 𝔮) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply B₁ S (Localization.AtPrime 𝔮), IsScalarTower.algebraMap_apply B₁ Sf S,
      ← IsScalarTower.algebraMap_apply Sf S (Localization.AtPrime 𝔮)])
  haveI : IsScalarTower B₁ B (Localization.AtPrime 𝔮) := IsScalarTower.of_algebraMap_eq (fun r => by
    rw [IsScalarTower.algebraMap_apply B₁ S (Localization.AtPrime 𝔮), IsScalarTower.algebraMap_apply B₁ B S,
      ← IsScalarTower.algebraMap_apply B S (Localization.AtPrime 𝔮)])
  set Q : Ideal B := 𝔮.comap (algebraMap B S) with hQdef
  haveI : Q.IsPrime := Ideal.IsPrime.comap _
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔮) Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization y.primeCompl (Localization.AtPrime 𝔮) 𝔮
  have hQy : Q ≤ y := by
    intro b hb
    by_contra hby
    have hu : IsUnit (algebraMap B S b) := (IsLocalization.map_units (Localization.AtPrime y) (⟨b, Ideal.mem_primeCompl_iff.mpr hby⟩ : y.primeCompl)).map eX.symm
    exact (Ideal.IsPrime.ne_top ‹𝔮.IsPrime›) (Ideal.eq_top_of_isUnit_mem _ hb hu)
  have hQ : ¬ Q.IsMaximal := by
    intro hQmax
    apply h𝔮
    have hQy' : Q = y := hQmax.eq_of_le (Ideal.IsPrime.ne_top ‹_›) hQy
    have hmS : IsLocalRing.maximalIdeal S ≤ 𝔮 := by
      intro s hs
      obtain ⟨⟨b, u⟩, hbu⟩ := IsLocalization.mk'_surjective y.primeCompl s
      have hbu' : IsLocalization.mk' S b u = s := hbu
      rw [← hbu'] at hs ⊢
      have hb : b ∈ y := (IsLocalization.AtPrime.mk'_mem_maximal_iff S y b u).mp hs
      rw [← hQy'] at hb
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact 𝔮.mul_mem_right _ hb
    have := (IsLocalRing.maximalIdeal.isMaximal S).eq_of_le (Ideal.IsPrime.ne_top ‹_›) hmS
    rw [← this]
    exact IsLocalRing.maximalIdeal.isMaximal S
  have hU : Algebra.FormallyUnramified B₁ (Localization.AtPrime Q) := hunr Q hQy hQ
  let e₁ : Localization.AtPrime Q ≃ₐ[B] Localization.AtPrime 𝔮 := IsLocalization.algEquiv Q.primeCompl _ _
  haveI : Algebra.FormallyUnramified B₁ (Localization.AtPrime 𝔮) := Algebra.FormallyUnramified.of_equiv (e₁.restrictScalars B₁)
  exact Algebra.FormallyUnramified.of_restrictScalars B₁ Sf (Localization.AtPrime 𝔮)

theorem E9.mem_valuationSubring_iff_of_under
    {O C : Type*} [CommRing O] [CommRing C] [Algebra O C]
    {K₂ K₁ : Type*} [Field K₂] [Field K₁] [Algebra O K₂] [Algebra C K₁]
    (ι₂ : K₂ →+* K₁) (hι₂ : ∀ o : O, ι₂ (algebraMap O K₂ o) = algebraMap C K₁ (algebraMap O C o))
    (Q : Ideal C) [Q.IsPrime]
    (V : ValuationSubring K₁)
    (hCV : ∀ c : C, algebraMap C K₁ c ∈ V)
    (hcen : ∀ c : C, algebraMap C K₁ c ∈ V.nonunits ↔ c ∈ Q)
    (V₂ : ValuationSubring K₂) (hPIR : IsPrincipalIdealRing ↥V₂)
    (hV₂mem : ∀ x : K₂, x ∈ V₂ ↔ ∃ c s : O, s ∉ Q.under O ∧ x * algebraMap O K₂ s = algebraMap O K₂ c)
    (t : O) (ht : t ∈ Q.under O) (ht0 : algebraMap O K₂ t ≠ 0) :
    ∀ y : K₂, y ∈ V₂ ↔ ι₂ y ∈ V := by
  classical

  have hunit : ∀ s : O, s ∉ Q.under O → algebraMap C K₁ (algebraMap O C s) ∉ V.nonunits :=
    fun s hs h => hs (Ideal.mem_comap.mpr ((hcen _).mp h))
  have hne : ∀ s : O, s ∉ Q.under O → algebraMap O K₂ s ≠ 0 := fun s hs h0 =>
    hunit s hs (by rw [← hι₂, h0, map_zero]; exact V.nonunits.zero_mem)
  have hfwd : ∀ y : K₂, y ∈ V₂ → ι₂ y ∈ V := by
    intro y hy
    obtain ⟨c, s, hs, hcs⟩ := (hV₂mem y).mp hy
    have hs0 : ι₂ (algebraMap O K₂ s) ≠ 0 := (map_ne_zero ι₂).mpr (hne s hs)
    have hinv : (ι₂ (algebraMap O K₂ s))⁻¹ ∈ V := by
      have h := hunit s hs
      rw [← hι₂, ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
      exact h.2
    have : ι₂ y = ι₂ (algebraMap O K₂ c) * (ι₂ (algebraMap O K₂ s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, hcs]
    rw [this]
    exact V.mul_mem _ _ (by rw [hι₂]; exact hCV _) hinv
  intro y
  refine ⟨hfwd y, fun hy => ?_⟩

  haveI : IsPrincipalIdealRing ↥V₂ := hPIR
  have hle : V₂ ≤ V.comap ι₂ := fun x hx => ValuationSubring.mem_comap.mpr (hfwd x hx)
  have hnt : V.comap ι₂ ≠ ⊤ := by
    intro htop
    have hmem : (algebraMap O K₂ t)⁻¹ ∈ V.comap ι₂ := htop ▸ ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, hι₂] at hmem
    have hnu : algebraMap C K₁ (algebraMap O C t) ∈ V.nonunits := (hcen _).mpr (Ideal.mem_comap.mp ht)
    rw [ValuationSubring.mem_nonunits_iff_or] at hnu
    rcases hnu with h0 | hni
    · apply ht0
      rw [← hι₂] at h0
      exact (map_eq_zero ι₂).mp h0
    · exact hni hmem
  have heq : V₂ = V.comap ι₂ := V₂.eq_of_le_of_ne_top hle hnt
  rw [heq, ValuationSubring.mem_comap]
  exact hy

theorem E9.residueField_transfer_of_under
    {O C : Type*} [CommRing O] [CommRing C] [Algebra O C]
    {K₂ K₁ : Type*} [Field K₂] [Field K₁] [Algebra O K₂] [Algebra C K₁]
    (ι₂ : K₂ →+* K₁) (hι₂ : ∀ o : O, ι₂ (algebraMap O K₂ o) = algebraMap C K₁ (algebraMap O C o))
    (Q : Ideal C) [Q.IsPrime]
    [Algebra (Localization.AtPrime (Q.under O)) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra (Q.under O) Q]
    (V : ValuationSubring K₁)
    (hCV : ∀ c : C, algebraMap C K₁ c ∈ V)
    (hcen : ∀ c : C, algebraMap C K₁ c ∈ V.nonunits ↔ c ∈ Q)
    (ιV : IsLocalRing.ResidueField ↥V ≃+* Q.ResidueField)
    (hιV : ∀ (c : C) (hc : algebraMap C K₁ c ∈ V),
      ιV (IsLocalRing.residue ↥V ⟨algebraMap C K₁ c, hc⟩) = algebraMap C Q.ResidueField c)
    (V₂ : ValuationSubring K₂)
    (hV₂mem : ∀ x : K₂, x ∈ V₂ ↔ ∃ c s : O, s ∉ Q.under O ∧ x * algebraMap O K₂ s = algebraMap O K₂ c)
    (ιV₂ : IsLocalRing.ResidueField ↥V₂ ≃+* (Q.under O).ResidueField)
    (hιV₂ : ∀ (c : O) (hc : algebraMap O K₂ c ∈ V₂),
      ιV₂ (IsLocalRing.residue ↥V₂ ⟨algebraMap O K₂ c, hc⟩) = algebraMap O (Q.under O).ResidueField c)
    (hV₂ : ∀ y : K₂, y ∈ V₂ ↔ ι₂ y ∈ V) :
    ∃ (_ : Algebra ↥V₂ ↥V) (_ : Algebra (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)),
      (∀ y : ↥V₂, (((algebraMap ↥V₂ ↥V y : ↥V) : K₁)) = ι₂ (y : K₂)) ∧
      (∀ y : ↥V₂, algebraMap (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)
        (IsLocalRing.residue ↥V₂ y) = IsLocalRing.residue ↥V (algebraMap ↥V₂ ↥V y)) ∧
      (Algebra.IsSeparable (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V) →
        Algebra.IsSeparable (Q.under O).ResidueField Q.ResidueField) := by
  classical

  let f : ↥V₂ →+* ↥V :=
    { toFun := fun y => ⟨ι₂ (y : K₂), (hV₂ y).mp y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hf : ∀ y : ↥V₂, ((f y : ↥V) : K₁) = ι₂ (y : K₂) := fun _ => rfl
  letI algV : Algebra ↥V₂ ↥V := f.toAlgebra
  haveI : IsLocalHom (algebraMap ↥V₂ ↥V) := ⟨fun y hy => by

    obtain ⟨b, hb⟩ := hy.exists_left_inv
    have hb' : ((b : ↥V) : K₁) * ι₂ (y : K₂) = 1 := by
      have := congrArg (fun z : ↥V => (z : K₁)) hb
      first | simpa [hf] using this | exact this | (simp only [RingHom.algebraMap_toAlgebra, hf] at this; exact this)
    have hy0 : (y : K₂) ≠ 0 := by
      intro h0
      rw [h0, map_zero, mul_zero] at hb'
      exact zero_ne_one hb'
    have hinv : (ι₂ (y : K₂))⁻¹ ∈ V := by
      rw [← eq_inv_of_mul_eq_one_left hb']; exact b.2
    have hyinv : (y : K₂)⁻¹ ∈ V₂ := (hV₂ _).mpr (by rw [map_inv₀]; exact hinv)
    exact IsUnit.of_mul_eq_one ⟨(y : K₂)⁻¹, hyinv⟩ (Subtype.ext (mul_inv_cancel₀ hy0))⟩
  refine ⟨algV, inferInstance, hf, fun y => rfl, fun hsep => ?_⟩
  haveI := hsep
  refine Algebra.IsSeparable.of_equiv_equiv ιV₂ ιV ?_

  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun y => ?_
  obtain ⟨c, s, hs, hcs⟩ := (hV₂mem y).mp y.2
  have h1 : (1 : O) ∉ Q.under O := fun h => (inferInstance : (Q.under O).IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hcV₂ : algebraMap O K₂ c ∈ V₂ := (hV₂mem _).mpr ⟨c, 1, h1, by simp⟩
  have hsV₂ : algebraMap O K₂ s ∈ V₂ := (hV₂mem _).mpr ⟨s, 1, h1, by simp⟩

  set F : IsLocalRing.ResidueField ↥V₂ →+* Q.ResidueField :=
    (algebraMap (Q.under O).ResidueField Q.ResidueField).comp (ιV₂ : IsLocalRing.ResidueField ↥V₂ →+* (Q.under O).ResidueField) with hF
  set G : IsLocalRing.ResidueField ↥V₂ →+* Q.ResidueField :=
    (ιV : IsLocalRing.ResidueField ↥V →+* Q.ResidueField).comp (algebraMap (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)) with hG

  have hFO : ∀ (o : O) (ho : algebraMap O K₂ o ∈ V₂), F (IsLocalRing.residue ↥V₂ ⟨_, ho⟩) = algebraMap C Q.ResidueField (algebraMap O C o) := by
    intro o ho
    rw [hF, RingHom.comp_apply, RingHom.coe_coe, hιV₂ o ho, ← IsScalarTower.algebraMap_apply O (Q.under O).ResidueField Q.ResidueField,
      IsScalarTower.algebraMap_apply O C Q.ResidueField]
  have hGO : ∀ (o : O) (ho : algebraMap O K₂ o ∈ V₂), G (IsLocalRing.residue ↥V₂ ⟨_, ho⟩) = algebraMap C Q.ResidueField (algebraMap O C o) := by
    intro o ho
    rw [hG, RingHom.comp_apply, IsLocalRing.ResidueField.algebraMap_residue, RingHom.coe_coe]
    have h2 : (algebraMap ↥V₂ ↥V ⟨algebraMap O K₂ o, ho⟩ : ↥V) = ⟨algebraMap C K₁ (algebraMap O C o), hCV _⟩ :=
      Subtype.ext (hι₂ o)
    rw [h2, hιV]

  have hys : (y * ⟨algebraMap O K₂ s, hsV₂⟩ : ↥V₂) = ⟨algebraMap O K₂ c, hcV₂⟩ := Subtype.ext hcs
  have hs0 : algebraMap C Q.ResidueField (algebraMap O C s) ≠ 0 := fun h0 =>
    hs (Ideal.mem_comap.mpr (Ideal.algebraMap_residueField_eq_zero.mp h0))
  show F (Ideal.Quotient.mk _ y) = G (Ideal.Quotient.mk _ y)
  have key : F (IsLocalRing.residue ↥V₂ y) * algebraMap C Q.ResidueField (algebraMap O C s) =
      G (IsLocalRing.residue ↥V₂ y) * algebraMap C Q.ResidueField (algebraMap O C s) := by
    conv_lhs => rw [← hFO s hsV₂, ← map_mul, ← map_mul, hys, hFO c hcV₂]
    conv_rhs => rw [← hGO s hsV₂, ← map_mul, ← map_mul, hys, hGO c hcV₂]
  exact mul_right_cancel₀ hs0 key

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem E9.vertical_core
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    {O C : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    [Algebra O C] [Module.Finite O C] [NoZeroSMulDivisors O C]
    [Algebra C ↥K₁] [IsFractionRing C ↥K₁] [Algebra O ↥K₂] [IsFractionRing O ↥K₂]
    [Algebra A C] [IsScalarTower A C ↥K₁]
    (hι₂O : ∀ o : O, (IntermediateField.inclusion hle).toRingHom (algebraMap O ↥K₂ o) = algebraMap C ↥K₁ (algebraMap O C o))
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal C) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A C ϖ ∈ Q)
    (t : O) (ht : t ∈ Q.under O) (ht0 : algebraMap O ↥K₂ t ≠ 0) (htϖ : algebraMap O C t = algebraMap A C ϖ)
    (hgauss : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      ∃ b : C, algebraMap C ↥K₁ b = Polynomial.aeval j P ∧ b ∉ Q) :
    Algebra.IsUnramifiedAt O Q := by
  classical

  letI locAlg : Algebra (Localization.AtPrime (Q.under O)) (Localization.AtPrime Q) :=
    (Localization.localRingHom (Q.under O) Q (algebraMap O C) Ideal.LiesOver.over).toAlgebra
  haveI : Localization.AtPrime.IsLiesOverAlgebra (Q.under O) Q := ⟨rfl⟩
  obtain ⟨hQ₂1, -, -, hiff⟩ :=
    Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one (O := O) (C := C) Q hQ1

  obtain ⟨V, -, hCV, hcen, hramiff, ιV, hιV⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := ↥K₁) Q hQ1

  have hVA : ∀ a : A, algebraMap A ↥K₁ a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply A C ↥K₁]
    exact hCV _
  have hϖV : algebraMap A ↥K₁ ϖ ∈ V.nonunits := by
    rw [IsScalarTower.algebraMap_apply A C ↥K₁]
    exact (hcen _).mpr hϖQ
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₁ a ∈ V.nonunits := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, ValuationSubring.mem_nonunits_iff, Valuation.map_mul]
    have h1 : V.valuation (algebraMap A ↥K₁ ϖ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hϖV
    have h2 : V.valuation (algebraMap A ↥K₁ c) ≤ 1 := V.valuation_le_one ⟨_, hVA c⟩
    calc V.valuation (algebraMap A ↥K₁ ϖ) * V.valuation (algebraMap A ↥K₁ c)
        ≤ V.valuation (algebraMap A ↥K₁ ϖ) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rwa [mul_one]
  have hVj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
    intro P hP
    obtain ⟨b, hb, hbQ⟩ := hgauss P hP
    have hmemV : Polynomial.aeval j P ∈ V := by rw [← hb]; exact hCV _
    have hnn : Polynomial.aeval j P ∉ V.nonunits := fun h => hbQ ((hcen _).mp (by rw [hb]; exact h))
    refine ⟨hmemV, ?_⟩
    rw [ValuationSubring.mem_nonunits_iff, not_lt] at hnn
    have heq : V.valuation (Polynomial.aeval j P) = 1 := le_antisymm (V.valuation_le_one ⟨_, hmemV⟩) hnn
    exact (V.valuation_le_one_iff _).mp (by rw [map_inv₀, heq, inv_one])
  refine hiff.mpr ⟨?_, ?_⟩
  ·
    have key := ModularCurve.XOneGammaZeroP.exists_eq_mul_of_mem_nonunits_valuationSubring_x1x0 p M hM hpM L ζ hζ K₁ hK₁ A hAp hζA
      j hj ϖ hϖ V hVA hVm hVj
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
        Ideal.span {algebraMap C (Localization.AtPrime Q) (algebraMap A C ϖ)} := by
      refine (hramiff _ hϖQ).mp ?_
      intro f hf
      obtain ⟨g, hg, rfl⟩ := key f hf
      exact ⟨g, hg, by rw [← IsScalarTower.algebraMap_apply]⟩
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : algebraMap O C x ∈ Q := by
        rw [Ideal.under_def, Ideal.mem_comap] at hx
        exact hx
      rw [Ideal.mem_comap]
      show algebraMap C (Localization.AtPrime Q) (algebraMap O C x) ∈ _
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hx'
    · rw [hmax, Ideal.span_singleton_le_iff_mem, ← htϖ]
      exact Ideal.mem_map_of_mem _ ht
  ·
    obtain ⟨V₂, hV₂mem, -, -, -, ιV₂, hιV₂⟩ :=
      IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := ↥K₂) (Q.under O) hQ₂1
    obtain ⟨V₂', hPIR', -, hV₂'mem⟩ :=
      IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one ↥K₂ (Q.under O) hQ₂1
    have hVV : V₂' = V₂ := by
      ext x
      rw [hV₂'mem, hV₂mem]
    subst hVV
    have hι₂ : ∀ y : ↥K₂, ((((IntermediateField.inclusion hle).toRingHom y : ↥K₁) : LaurentSeries L)) =
        ((y : ↥K₂) : LaurentSeries L) := fun _ => rfl
    have hV₂ : ∀ y : ↥K₂, y ∈ V₂' ↔ (IntermediateField.inclusion hle).toRingHom y ∈ V :=
      E9.mem_valuationSubring_iff_of_under (IntermediateField.inclusion hle).toRingHom hι₂O Q V hCV hcen V₂' hPIR' hV₂mem t ht ht0
    obtain ⟨algV, algκ, halgV, hres, htransfer⟩ :=
      E9.residueField_transfer_of_under (IntermediateField.inclusion hle).toRingHom hι₂O Q V hCV hcen ιV hιV V₂' hV₂mem ιV₂ hιV₂ hV₂
    letI := algV
    letI := algκ
    obtain ⟨-, hsepres⟩ :=
      ModularCurve.XOneGammaZeroP.finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
        p M hM hpM L ζ hζ K₁ hK₁ K₂ hK₂ (IntermediateField.inclusion hle).toRingHom hι₂ A hAp hζA j hj V hVA hVm hVj V₂' hV₂ halgV hres
    exact htransfer hsepres

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem E9.vertical
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁] [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (htj : Transcendental A j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁)
    (j₂ : ↥K₂) [Fact (j₂ ≠ 0)]
    (ιF₂ : ↥(chartAlgFin A (↥K₂) j₂) →ₐ[A] ↥(chartAlgFin A (↥K₁) j))
    (hιF₂ : ∀ x, (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L))
    [Algebra ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j)]
    (halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) x = ιF₂ x)
    [Module.Finite ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j)]
    [IsFractionRing ↥(chartAlgFin A (↥K₁) j) ↥K₁] [IsFractionRing ↥(chartAlgFin A (↥K₂) j₂) ↥K₂]
    [IsNoetherianRing ↥(chartAlgFin A (↥K₁) j)] [IsNoetherianRing ↥(chartAlgFin A (↥K₂) j₂)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal ↥(chartAlgFin A (↥K₁) j)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ Q) :
    Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K₂) j₂) Q := by
  classical
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₁) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K₁ {j}
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₂) j₂) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K₂ {j₂}
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) := IsScalarTower.of_algebraMap_eq fun a => by rw [halg, ιF₂.commutes]
  have hinj : Function.Injective (algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j)) := by
    intro a b h
    rw [halg, halg] at h
    apply Subtype.ext; apply Subtype.ext
    rw [← hιF₂ a, ← hιF₂ b, h]
  haveI : NoZeroSMulDivisors ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun hc => hinj (by rw [map_zero]; exact hc)⟩

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖprime : Prime ϖ := hϖirr.prime
  have hAB : Function.Injective (algebraMap A ↥(chartAlgFin A (↥K₁) j)) := by
    intro a b h
    have h' := congrArg (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A L ↥K₁, IsScalarTower.algebraMap_apply A L ↥K₁] at h'
    exact IsFractionRing.injective A L ((algebraMap L ↥K₁).injective h')
  have hϖB0 : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hAB]
    exact hϖprime.ne_zero
  have htϖ : algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ :=
    (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) ϖ).symm
  have hϖ₂ : algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ ∈ Q.under ↥(chartAlgFin A (↥K₂) j₂) := by
    rw [Ideal.under_def, Ideal.mem_comap, htϖ]
    exact hϖQ
  have hϖK₂ : algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥K₂ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ↥(chartAlgFin A (↥K₂) j₂) ↥K₂)]
    intro h
    apply hϖB0
    rw [← htϖ, h, map_zero]
  have hι₂O : ∀ o : ↥(chartAlgFin A (↥K₂) j₂), (IntermediateField.inclusion hle).toRingHom (algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥K₂ o) =
      algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ (algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) o) := by
    intro o
    apply Subtype.ext
    rw [halg]
    exact (hιF₂ o).symm

  have hQmin : Q ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ}).minimalPrimes := by
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

  obtain ⟨V', -, -, hcen', -, hVj'⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin A L ↥K₁ j htj hFD hsep
      ϖ hϖprime Q hQmin
  have hcoe : ∀ P : Polynomial A, ((Polynomial.aeval (jChartFin A (↥K₁) j) P : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = Polynomial.aeval j P := by
    intro P
    exact (Polynomial.aeval_algHom_apply (chartAlgFin A (↥K₁) j).val (jChartFin A (↥K₁) j) P).symm
  have hgauss : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      ∃ b : ↥(chartAlgFin A (↥K₁) j), algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ b = Polynomial.aeval j P ∧ b ∉ Q := by
    intro P hP
    have hndvd : ¬ (Polynomial.C ϖ ∣ P) := by
      intro hdvd
      apply hP
      obtain ⟨R, rfl⟩ := hdvd
      rw [Polynomial.map_mul, Polynomial.map_C]
      have : IsLocalRing.residue A ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr (by
        rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
      rw [this, Polynomial.C_0, zero_mul]
    refine ⟨Polynomial.aeval (jChartFin A (↥K₁) j) P, hcoe P, fun hmem => ?_⟩
    obtain ⟨-, hinv⟩ := hVj' P hndvd
    have hnu : ((Polynomial.aeval (jChartFin A (↥K₁) j) P : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) ∈ V'.nonunits := (hcen' _).mp hmem
    rw [hcoe] at hnu
    have hP0 : P ≠ 0 := fun h => hndvd (h ▸ dvd_zero _)
    have hx0 : Polynomial.aeval j P ≠ 0 := fun h => hP0 ((transcendental_iff_injective.mp htj) (by rw [h, map_zero]))
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp hnu
    have hle' := (V'.valuation_le_one_iff _).mpr hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0))] at hle'
    exact absurd hlt (not_lt.mpr hle')
  exact E9.vertical_core p M hM hpM L ζ hζ K₁ hK₁ K₂ hK₂ hle A hAp hζA j hj hι₂O ϖ hϖ Q hQ1 hϖQ
    (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) hϖ₂ hϖK₂ htϖ hgauss

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem E9.horizontal
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (hp2 : p ≠ 2 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) (hlev3 : p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1)
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁] [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (htj : Transcendental A j)
    (j₂ : ↥K₂) [Fact (j₂ ≠ 0)]
    (ιF₂ : ↥(chartAlgFin A (↥K₂) j₂) →ₐ[A] ↥(chartAlgFin A (↥K₁) j))
    (hιF₂ : ∀ x, (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L))
    [Algebra ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j)]
    (halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) x = ιF₂ x)
    [Module.Finite ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j)]
    [IsFractionRing ↥(chartAlgFin A (↥K₁) j) ↥K₁] [IsFractionRing ↥(chartAlgFin A (↥K₂) j₂) ↥K₂]
    [IsNoetherianRing ↥(chartAlgFin A (↥K₂) j₂)]
    (hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Q : Ideal ↥(chartAlgFin A (↥K₁) j)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hϖQ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∉ Q)
    (hd0 : jChartFin A (↥K₁) j ∈ Q → p % 3 ≠ 1) (hd1728 : jChartFin A (↥K₁) j - 1728 ∈ Q → p % 4 ≠ 1) :
    Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K₂) j₂) Q := by
  classical
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₁) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K₁ {j}
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₂) j₂) := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A ↥K₂ {j₂}
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) :=
    IsScalarTower.of_algebraMap_eq fun a => by rw [halg, ιF₂.commutes]
  let φ : ↥K₂ →ₐ[L] ↥K₁ := IntermediateField.inclusion hle
  have hι : ∀ x : ↥(chartAlgFin A (↥K₂) j₂),
      algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ (algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) x) =
        φ (algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥K₂ x) := by
    intro x
    rw [halg]
    apply Subtype.ext
    show (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L)
    exact hιF₂ x
  have hjB : algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ (jChartFin A (↥K₁) j) = j := rfl
  have hjB' : algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ (jChartFin A (↥K₁) j - 1728) = j - 1728 := by
    rw [map_sub, map_ofNat, hjB]
  have hJ0 : jChartFin A (↥K₁) j ≠ 0 := fun h => (Fact.out : j ≠ 0) (by rw [← hjB, h, map_zero])
  have hJ1728 : jChartFin A (↥K₁) j - 1728 ≠ 0 := by
    intro h
    apply htj
    have : j = algebraMap A ↥K₁ 1728 := by
      rw [map_ofNat]
      exact sub_eq_zero.mp (by rw [← hjB', h, map_zero])
    rw [this]
    exact isAlgebraic_algebraMap _
  have he : ∀ w : AlgebraicCurve.Place L ↥K₁,
      (∀ r : ↥(chartAlgFin A (↥K₁) j), 0 ≤ w.ord (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ r)) →
      (∀ r : ↥(chartAlgFin A (↥K₁) j), r ≠ 0 → (0 < w.ord (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥K₁ r) ↔ r ∈ Q)) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1 := by
    intro w hw0 hwQ
    have hx : 0 ≤ w.ord j := hjB ▸ hw0 _
    have h0 : 0 < w.ord j → p % 3 ≠ 1 ∧ (p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1) := fun hpos =>
      ⟨hd0 ((hwQ _ hJ0).mp (by rw [hjB]; exact hpos)), hlev3⟩
    have h1728 : 0 < w.ord (j - 1728) → p % 4 ≠ 1 ∧ (p = 2 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) := fun hpos =>
      ⟨hd1728 ((hwQ _ hJ1728).mp (by rw [hjB']; exact hpos)), fun hp => hp2.resolve_left (fun h => h hp)⟩
    obtain ⟨t, htK₂, ht1⟩ :=
      ModularCurve.exists_ord_eq_one_of_place_x1x0FunctionFieldC_gamma0_of_ord_nonneg_of_tame p M hM hpM L K₁ hK₁ K₂ hK₂ j hj w hx
        h0 h1728
    have hφt : φ ⟨(t : LaurentSeries L), htK₂⟩ = t := Subtype.ext rfl
    have h := AlgebraicCurve.Place.ord_restrictAlong φ hint w ⟨(t : LaurentSeries L), htK₂⟩
    rw [hφt, ht1] at h
    have h0' : (0 : ℤ) ≤ (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) := Int.natCast_nonneg _
    exact_mod_cast Int.eq_one_of_mul_eq_one_right h0' h.symm
  exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre L A ↥K₁ ↥K₂ φ
    ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K₂) j₂) hι hint Q hQ1 he ϖ hϖ hϖQ

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem E9.chart
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (hp2 : p ≠ 2 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) (hlev3 : p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (ιF₂ : ↥(chartAlgFin A (↥K₂) j₂) →ₐ[A] ↥(chartAlgFin A (↥K₁) j))
    (hιF₂ : ∀ x, (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L))
    (hιF₂fin : ιF₂.toRingHom.Finite)
    (y : ↥(XFin A (↥K₁) j))
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₁) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K₁) j) ∈ ModularCurve.ssJSet p Ω)
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal) :
    letI : Algebra ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) := ιF₂.toRingHom.toAlgebra
    ∀ (Q : Ideal ↥(chartAlgFin A (↥K₁) j)) [Q.IsPrime], Q ≤ y.asIdeal → ¬ Q.IsMaximal → Algebra.IsUnramifiedAt ↥(chartAlgFin A (↥K₂) j₂) Q := by
  classical
  intro Q _ hQy hQmax
  letI instAlg : Algebra ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) := ιF₂.toRingHom.toAlgebra
  have halg : ∀ x, algebraMap ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) x = ιF₂ x := fun _ => rfl

  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₁ A j hj
  have htj₂ : Transcendental A j₂ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₂ A j₂ hj₂
  have hT1 : ∀ N : ℕ, ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := fun N => by
    rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]
  have hT0 : ∀ N : ℕ, ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := fun N => by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Nat.Prime.ne_zero Fact.out)⟩
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) ⟨hT1 _, hT0 _⟩ L K₁ hK₁ j hj
  have hFD₂ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 (M * p)) (hT0 _) L K₂ hK₂ j₂ hj₂
  haveI := hFD
  haveI := hFD₂
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K₁)) ↥K₁ := inferInstance
  have hsep₂ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ := inferInstance
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₁) j) := by
    haveI := (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L ↥K₁ j htj hFD hsep).1
    exact Algebra.FiniteType.isNoetherianRing A ↥(chartAlgFin A (↥K₁) j)
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₂) j₂) := by
    haveI := (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L ↥K₂ j₂ htj₂ hFD₂ hsep₂).1
    exact Algebra.FiniteType.isNoetherianRing A ↥(chartAlgFin A (↥K₂) j₂)
  haveI : IsFractionRing ↥(chartAlgFin A (↥K₁) j) ↥K₁ := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L ↥K₁ {j}
  haveI : IsFractionRing ↥(chartAlgFin A (↥K₂) j₂) ↥K₂ := AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L ↥K₂ {j₂}
  haveI : Module.Finite ↥(chartAlgFin A (↥K₂) j₂) ↥(chartAlgFin A (↥K₁) j) := hιF₂fin

  have hjK₂ : ((j : LaurentSeries L)) ∈ K₂ := by rw [hj, ← hj₂]; exact j₂.2
  have hint : (IntermediateField.inclusion hle).toRingHom.IsIntegral := E9.isIntegral_inclusion L K₁ K₂ hle j hjK₂ hFD

  by_cases hQ0 : Q = ⊥
  · subst hQ0
    exact E9.generic_point L K₁ K₂ hle A j j₂ ιF₂ hιF₂ halg hint

  have hQ1 : Q.height = 1 :=
    Ideal.height_eq_one_of_ne_bot_of_not_isMaximal_of_ringKrullDim_le_two
      (E9.ringKrullDim_chartAlgFin_le_two A ↥K₁ j htj) Q hQ0 hQmax
  by_cases hϖQ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ Q
  ·
    exact E9.vertical p M hM hpM L ζ hζ K₁ hK₁ K₂ hK₂ hle A hAp hζA j hj htj hFD hsep j₂ ιF₂ hιF₂ halg ϖ hϖ Q hQ1 hϖQ
  ·
    have hpy : algebraMap A ↥(chartAlgFin A (↥K₁) j) p ∈ y.asIdeal := by
      have hpA : (p : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAp
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpA
      rw [← hc, map_mul]
      exact Ideal.mul_mem_left _ _ hyϖ
    obtain ⟨hd0, hd1728⟩ := E9.deuring_of_ssToken p j y hpy hss Q hQy
    exact E9.horizontal p M hM hpM hp2 hlev3 L K₁ hK₁ K₂ hK₂ hle A j hj htj j₂ ιF₂ hιF₂ halg hint ϖ hϖ Q hQ1 hϖQ hd0 hd1728

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (hp2 : p ≠ 2 ∨ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 4 ≠ 1) (hlev3 : p = 3 → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (hle : K₂ ≤ K₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (π₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j) ⟶ (AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂))
    (ιF₂ : ↥(chartAlgFin A (↥K₂) j₂) →ₐ[A] ↥(chartAlgFin A (↥K₁) j))
    (hιF₂ : ∀ x, (((ιF₂ x : ↥K₁) : LaurentSeries L)) = ((x : ↥K₂) : LaurentSeries L))
    (hπbase : π₂ ≫ toBase A (↥K₂) j₂ = toBase A (↥K₁) j)
    (hπF : Spec.map (CommRingCat.ofHom ιF₂.toRingHom) ≫ ιFin A (↥K₂) j₂ = ιFin A (↥K₁) j ≫ π₂)
    (hpreF : π₂ ⁻¹ᵁ (ιFin A (↥K₂) j₂).opensRange = (ιFin A (↥K₁) j).opensRange)
    (hπfin : IsFinite π₂) (hιF₂fin : ιF₂.toRingHom.Finite)
    (hintF : ∀ x : ↥K₁, x ∈ chartAlgFin A (↥K₁) j ↔ IsIntegral ↥((ιF₂.range).map (chartAlgFin A (↥K₁) j).val) x)

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z)
    (hϖz : ϖz = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.germ ⊤ z trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₁) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z))
    (y : ↥(XFin A (↥K₁) j)) (hy : (ιFin A (↥K₁) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₁) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K₁) j) ∈ ModularCurve.ssJSet p Ω) :
    letI : Algebra ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)) ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z) := (π₂.stalkMap z).hom.toAlgebra
    ∀ (𝔮 : Ideal ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z)) [𝔮.IsPrime], ¬ 𝔮.IsMaximal →
      Algebra.IsUnramifiedAt ↑((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk (π₂.base z)) 𝔮 := by
  classical
  subst hy
  haveI : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨eX, eY, heX, -, hdict⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom A (↥K₁) j (↥K₂) j₂ ιF₂ π₂ hπF y
  obtain ⟨eXr, eYr, heXr, -, hdict'⟩ := E9.exists_ringEquiv_pair _ eX eY _ hdict

  have hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal :=
    E9.algebraMap_mem_of_mem_maximalIdeal y.asIdeal eXr ϖz hz ϖ (by rw [heXr, hϖz]; exact heX ϖ)
  exact E9.isUnramifiedAt_stalk_of_chart ιF₂.toRingHom y.asIdeal
    (E9.chart p M hM hpM hp2 hlev3 L ζ hζ K₁ hK₁ K₂ hK₂ hle A hAp hζA j hj j₂ hj₂ ϖ hϖ ιF₂ hιF₂ hιF₂fin y hss hyϖ)
    (π₂.stalkMap ((ιFin A (↥K₁) j).base y)).hom eXr eYr hdict'

end S_ModularCurve_XOneGammaZeroP_isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame
end P2MW
export P2MW.S_ModularCurve_XOneGammaZeroP_isUnramifiedAt_stalk_of_not_isMaximal_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0_of_tame (solution)
