-- Prove2me | solution 1 for ModularCurve.exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b5990fc1-f681-5026-88e2-1c17941fdb9b

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_GaloisLattice_exists_trace_det_of_basis_fin_two_of_frobenius_relations
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jH
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Theorems.Thm_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion
import Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH
import Theorems.Thm_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH
import Theorems.Thm_ModularCurve_diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par Ihara.instGroupIharaAmalgam CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP"
p2m_attr_erase "simp" "ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one"
p2m_attr_erase "simp" "HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero"
p2m_attr_erase "simp" "CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left"

open scoped TensorProduct

set_option autoImplicit false

namespace TMatPkg

theorem idem_mul_trace_det_eq_of_span
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (f : V →ₗ[R] V) {ε : R} (hε : IsIdempotentElem ε) (s : R)
    (X Y : V) (hspan : ∀ j : Fin 2, ∃ u w : R, ε • b j = u • X + w • Y)
    (a b' c d : R) (hfX : s • f X = a • X + c • Y) (hfY : s • f Y = b' • X + d • Y) :
    ε * (s * (b.repr (f (b 0)) 0 + b.repr (f (b 1)) 1)) = ε * (a + d) ∧
      ε * (s ^ 2 * (b.repr (f (b 0)) 0 * b.repr (f (b 1)) 1 - b.repr (f (b 1)) 0 * b.repr (f (b 0)) 1))
        = ε * (a * d - b' * c) := by
  classical
  set Mf : Matrix (Fin 2) (Fin 2) R := LinearMap.toMatrix b b f with hMf
  have htr : b.repr (f (b 0)) 0 + b.repr (f (b 1)) 1 = Mf.trace := by
    rw [hMf, Matrix.trace_fin_two, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hdt : b.repr (f (b 0)) 0 * b.repr (f (b 1)) 1 - b.repr (f (b 1)) 0 * b.repr (f (b 0)) 1 = Mf.det := by
    rw [hMf, Matrix.det_fin_two, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  rw [htr, hdt]

  let v : Fin 2 → V := ![X, Y]
  let Q : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => b.repr (v j) i
  choose u w hu using hspan
  let P' : Matrix (Fin 2) (Fin 2) R := !![u 0, u 1; w 0, w 1]
  let G : Matrix (Fin 2) (Fin 2) R := !![a, b'; c, d]
  have hQ0 : ∀ i, Q i 0 = b.repr X i := fun i => rfl
  have hQ1 : ∀ i, Q i 1 = b.repr Y i := fun i => rfl

  have hQP' : Q * P' = ε • (1 : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    have h := congrArg (fun z => b.repr z i) (hu j)
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_apply] at h
    have hP0 : P' 0 j = u j := by fin_cases j <;> rfl
    have hP1 : P' 1 j = w j := by fin_cases j <;> rfl
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hP0,
      hP1, hQ0, hQ1, mul_comm _ (u j), mul_comm _ (w j), ← h]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (Ne.symm hij)]

  have hf : ∀ j : Fin 2, s • f (v j) = G 0 j • X + G 1 j • Y := by
    intro j
    fin_cases j
    · exact hfX
    · exact hfY
  have hMQ : s • (Mf * Q) = Q * G := by
    ext i j
    have e1 : (Mf * Q) i j = b.repr (f (v j)) i := by
      rw [hMf, ← LinearMap.toMatrix_mulVec_repr b b f (v j)]
      rfl
    have h := congrArg (fun z => b.repr z i) (hf j)
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
    rw [Matrix.smul_apply, smul_eq_mul, e1, h, Matrix.mul_apply, Fin.sum_univ_two, hQ0, hQ1]
    ring

  set P : Matrix (Fin 2) (Fin 2) R := ε • P' with hP
  have hQP : Q * P = ε • (1 : Matrix (Fin 2) (Fin 2) R) := by
    rw [hP, Matrix.mul_smul, hQP', smul_smul, hε.eq]
  have hεP : ε • P = P := by rw [hP, smul_smul, hε.eq]
  have hdetQP : Q.det * P.det = ε := by
    rw [← Matrix.det_mul, hQP, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
      hε.pow_succ_eq]
  have hPQ : P * Q = ε • (1 : Matrix (Fin 2) (Fin 2) R) := by
    have h1 : Q.det • P = ε • Q.adjugate :=
      calc Q.det • P = (Q.det • (1 : Matrix (Fin 2) (Fin 2) R)) * P := by
              rw [smul_mul_assoc, Matrix.one_mul]
        _ = Q.adjugate * Q * P := by rw [Matrix.adjugate_mul]
        _ = Q.adjugate * (ε • 1) := by rw [Matrix.mul_assoc, hQP]
        _ = ε • Q.adjugate := by rw [Matrix.mul_smul, Matrix.mul_one]
    have h2 : Q.det • (P * Q) = (ε * Q.det) • (1 : Matrix (Fin 2) (Fin 2) R) :=
      calc Q.det • (P * Q) = (Q.det • P) * Q := (smul_mul_assoc _ _ _).symm
        _ = (ε • Q.adjugate) * Q := by rw [h1]
        _ = ε • (Q.adjugate * Q) := smul_mul_assoc _ _ _
        _ = (ε * Q.det) • 1 := by rw [Matrix.adjugate_mul, smul_smul]
    have h3 : (P.det * Q.det) • (P * Q) = (P.det * (ε * Q.det)) • (1 : Matrix (Fin 2) (Fin 2) R) := by
      rw [mul_smul, mul_smul P.det, h2]
    rw [mul_comm P.det Q.det, hdetQP, mul_left_comm P.det ε Q.det, mul_comm P.det Q.det, hdetQP,
      hε.eq, ← smul_mul_assoc, hεP] at h3
    exact h3
  refine ⟨?_, ?_⟩
  ·
    have e1 : ε * (s * Mf.trace) = (s • Mf * (Q * P)).trace := by
      rw [hQP, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
        smul_eq_mul]
    rw [e1, ← Matrix.mul_assoc, Matrix.smul_mul, hMQ, Matrix.trace_mul_cycle, hPQ, Matrix.smul_mul,
      Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_fin_two]
    rfl
  ·
    have e1 : ε * (s ^ 2 * Mf.det) = (s • Mf).det * (Q.det * P.det) := by
      rw [hdetQP, Matrix.det_smul, Fintype.card_fin, mul_comm]
    rw [e1, ← mul_assoc, ← Matrix.det_mul, Matrix.smul_mul, hMQ, Matrix.det_mul, mul_comm Q.det,
      mul_assoc, hdetQP, mul_comm _ ε, Matrix.det_fin_two]
    rfl

section Abstract

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T]

abbrev V (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] : Type :=
  ℚ_[p] ⊗[ℤ_[p]] T

noncomputable def toV (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T] :
    T →ₗ[ℤ_[p]] V p T :=
  TensorProduct.mk ℤ_[p] ℚ_[p] T 1

theorem toV_apply (x : T) : toV p T x = (1 : ℚ_[p]) ⊗ₜ x := rfl

theorem toV_smul (z : ℤ_[p]) (x : T) : toV p T (z • x) = (z : ℚ_[p]) • toV p T x := by
  rw [LinearMap.map_smul]
  exact (algebraMap_smul ℚ_[p] z (toV p T x)).symm

theorem toV_pow_smul (n : ℕ) (x : T) :
    toV p T (((p : ℤ_[p]) ^ n) • x) = ((p : ℚ_[p]) ^ n) • toV p T x := by
  rw [toV_smul, PadicInt.coe_pow, PadicInt.coe_natCast]

theorem baseChange_toV (f : Module.End ℤ_[p] T) (x : T) : f.baseChange ℚ_[p] (toV p T x) = toV p T (f x) :=
  rfl

theorem toV_injective [Module.Free ℤ_[p] T] : Function.Injective (toV p T) := by
  have h1 : Function.Injective (Algebra.linearMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := T)
    (Algebra.linearMap ℤ_[p] ℚ_[p]) h1
  intro x y hxy
  have : (Algebra.linearMap ℤ_[p] ℚ_[p]).rTensor T ((TensorProduct.lid ℤ_[p] T).symm x) =
      (Algebra.linearMap ℤ_[p] ℚ_[p]).rTensor T ((TensorProduct.lid ℤ_[p] T).symm y) := by
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  exact (TensorProduct.lid ℤ_[p] T).symm.injective (h2 this)

theorem exists_pow_mul_eq_coe (a : ℚ_[p]) : ∃ (k : ℕ) (z : ℤ_[p]), (p : ℚ_[p]) ^ k * a = z := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖a‖ ≤ (p : ℝ) ^ k := by
    have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖a‖ hp
    exact ⟨k, hk.le⟩
  have hnorm : ‖(p : ℚ_[p]) ^ k * a‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Padic.norm_p]
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    rw [inv_pow, ← div_eq_inv_mul, div_le_one (pow_pos hp0 k)]
    exact hk
  exact ⟨k, ⟨_, hnorm⟩, rfl⟩

theorem exists_pow_smul_eq_toV (v : V p T) :
    ∃ (k : ℕ) (x : T), ((p : ℚ_[p]) ^ k) • v = toV p T x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by rw [map_zero, smul_zero]⟩
  | tmul a x =>
    obtain ⟨k, z, hz⟩ := exists_pow_mul_eq_coe (p := p) a
    refine ⟨k, z • x, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, hz, toV_smul, toV_apply,
      TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    rfl
  | add v w hv hw =>
    obtain ⟨k, x, hx⟩ := hv
    obtain ⟨j, y, hy⟩ := hw
    refine ⟨k + j, ((p : ℤ_[p]) ^ j) • x + ((p : ℤ_[p]) ^ k) • y, ?_⟩
    rw [map_add, toV_pow_smul, toV_pow_smul, ← hx, ← hy, smul_smul, smul_smul, ← pow_add, ← pow_add,
      add_comm j k, smul_add]

variable {ι₀ : Type} (A : ι₀ → Module.End ℤ_[p] T)

noncomputable abbrev R (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T]
    (A : ι₀ → Module.End ℤ_[p] T) : Subalgebra ℚ_[p] (Module.End ℚ_[p] (V p T)) :=
  Algebra.adjoin ℚ_[p] (Set.range fun g : ι₀ => (A g).baseChange ℚ_[p])

variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

noncomputable def ψ (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[p] T]
    (𝕋 : Type) [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T] :
    𝕋 →ₐ[ℤ_[p]] Module.End ℚ_[p] (V p T) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] T).comp (Algebra.lsmul ℤ_[p] ℤ_[p] T)

theorem ψ_apply (t : 𝕋) : ψ p T 𝕋 t = (Algebra.lsmul ℤ_[p] ℤ_[p] T t).baseChange ℚ_[p] := rfl

theorem ψ_toV (t : 𝕋) (x : T) : ψ p T 𝕋 t (toV p T x) = toV p T (t • x) := rfl

theorem ψ_injective [Module.Free ℤ_[p] T] (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0) :
    Function.Injective (ψ p T 𝕋) := by
  intro s t hst
  rw [← sub_eq_zero]
  refine hfaith _ fun x => ?_
  have h := LinearMap.congr_fun hst (toV p T x)
  rw [ψ_toV, ψ_toV] at h
  rw [sub_smul, sub_eq_zero]
  exact toV_injective h

theorem pow_smul_ψ (n : ℕ) (u : 𝕋) :
    ((p : ℚ_[p]) ^ n) • ψ p T 𝕋 u = ψ p T 𝕋 (((p : ℤ_[p]) ^ n) • u) := by
  rw [map_smul, ← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ n) (ψ p T 𝕋 u), map_pow, map_natCast]

variable (op : ι₀ → 𝕋)

theorem ψ_op (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) (g : ι₀) :
    ψ p T 𝕋 (op g) = (A g).baseChange ℚ_[p] := by
  rw [ψ_apply]
  congr 1
  exact LinearMap.ext (hop g)

theorem ψ_mem_R (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤) (t : 𝕋) : ψ p T 𝕋 t ∈ R p T A := by
  have ht : t ∈ Algebra.adjoin ℤ_[p] (Set.range op) := by rw [hgen]; exact Algebra.mem_top
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [ψ_op A op hop]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] _ r]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

theorem isMulCommutative_R (hop : ∀ (g : ι₀) (x : T), op g • x = A g x) :
    IsMulCommutative (R p T A) := by
  refine Algebra.isMulCommutative_adjoin ℚ_[p] ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  show (A i).baseChange ℚ_[p] * (A j).baseChange ℚ_[p] = (A j).baseChange ℚ_[p] * (A i).baseChange ℚ_[p]
  rw [← ψ_op A op hop, ← ψ_op A op hop, ← map_mul, ← map_mul, mul_comm]

variable {G : Type} [Group G] (ρ : G →* Module.End ℤ_[p] T)

theorem commute_ρ (hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)) (σ : G)
    {r : Module.End ℚ_[p] (V p T)} (hr : r ∈ R p T A) :
    r * (ρ σ).baseChange ℚ_[p] = (ρ σ).baseChange ℚ_[p] * r := by
  have hle : R p T A ≤ Subalgebra.centralizer ℚ_[p] {(ρ σ).baseChange ℚ_[p]} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩ _ rfl
    show (ρ σ).baseChange ℚ_[p] * (A i).baseChange ℚ_[p] = (A i).baseChange ℚ_[p] * (ρ σ).baseChange ℚ_[p]
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul]
    congr 1
    exact LinearMap.ext fun x => hcomm σ i x
  exact ((Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle hr) _ rfl).symm

noncomputable def ρR (hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)) (σ : G) :
    V p T →ₗ[R p T A] V p T where
  toFun := (ρ σ).baseChange ℚ_[p]
  map_add' := map_add _
  map_smul' r v := by
    show (ρ σ).baseChange ℚ_[p] ((r : Module.End ℚ_[p] (V p T)) v)
      = (r : Module.End ℚ_[p] (V p T)) ((ρ σ).baseChange ℚ_[p] v)
    rw [← Module.End.mul_apply, ← commute_ρ A ρ hcomm σ r.2, Module.End.mul_apply]

variable {A ρ}

theorem ρR_apply {hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x)} (σ : G) (v : V p T) :
    ρR A ρ hcomm σ v = (ρ σ).baseChange ℚ_[p] v := rfl

theorem smul_R_apply (r : R p T A) (v : V p T) : r • v = (r : Module.End ℚ_[p] (V p T)) v := rfl

theorem qsmul_R_smul (c : ℚ_[p]) (r : R p T A) (v : V p T) : (c • r) • v = c • (r • v) := rfl

section Lattice

variable [IsMulCommutative (R p T A)]

open scoped IsMulCommutative in

noncomputable local instance (priority := high) instCommRingR : CommRing (R p T A) :=
  IsMulCommutative.instCommRing

theorem lattice [Module.Free ℤ_[p] T]
    (hcomm : ∀ (σ : G) (g : ι₀) (x : T), ρ σ (A g x) = A g (ρ σ x))
    (b : Module.Basis (Fin 2) (R p T A) (V p T)) (hop : ∀ (g : ι₀) (x : T), op g • x = A g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0) (σ : G) (t d : 𝕋)
    (ht : ψ p T 𝕋 t = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1))
    (hd : ψ p T 𝕋 d = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
      - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1))
    {e : 𝕋} (he : IsIdempotentElem e) (x y : T) (N : ℕ)
    (hspan : ∀ z : T, ∃ a c : 𝕋, ((p : ℤ_[p]) ^ N) • (e • z) = a • x + c • y)
    (a b' c d' : 𝕋) (hx : ((p : ℤ_[p]) ^ N) • ρ σ x = a • x + c • y)
    (hy : ((p : ℤ_[p]) ^ N) • ρ σ y = b' • x + d' • y) :
    e * ((p : 𝕋) ^ N * t) = e * (a + d') ∧
      e * ((p : 𝕋) ^ (2 * N) * d) = e * (a * d' - b' * c) := by
  have hψinj := ψ_injective (p := p) (T := T) (𝕋 := 𝕋) hfaith

  let ι : 𝕋 → R p T A := fun u => ⟨ψ p T 𝕋 u, ψ_mem_R A op hop hgen u⟩
  have hιinj : Function.Injective ι := fun u u' h => hψinj (congrArg Subtype.val h)
  have hι_smul : ∀ (u : 𝕋) (z : T), ι u • toV p T z = toV p T (u • z) := fun u z => rfl
  have hι_add : ∀ u u', ι (u + u') = ι u + ι u' := fun u u' => Subtype.ext (map_add _ u u')
  have hι_mul : ∀ u u', ι (u * u') = ι u * ι u' := fun u u' => Subtype.ext (map_mul _ u u')
  have hι_sub : ∀ u u', ι (u - u') = ι u - ι u' := fun u u' => Subtype.ext (map_sub _ u u')
  have hε : IsIdempotentElem (ι e) := by
    show ι e * ι e = ι e
    rw [← hι_mul, he.eq]

  let s : R p T A := algebraMap ℚ_[p] (R p T A) ((p : ℚ_[p]) ^ N)
  have hs : ∀ v : V p T, s • v = ((p : ℚ_[p]) ^ N) • v := fun v => by
    rw [smul_R_apply, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply]
  have hsι : ∀ u : 𝕋, s * ι u = ι ((p : 𝕋) ^ N * u) := fun u => Subtype.ext (by
    show algebraMap ℚ_[p] (Module.End ℚ_[p] (V p T)) ((p : ℚ_[p]) ^ N) * ψ p T 𝕋 u
      = ψ p T 𝕋 ((p : 𝕋) ^ N * u)
    rw [← Algebra.smul_def, pow_smul_ψ, Algebra.smul_def, map_pow, map_natCast])

  have hιt : ι t = b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1 :=
    Subtype.ext ht
  have hιd : ι d = b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
      - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1 :=
    Subtype.ext hd

  have hspanV : ∀ j : Fin 2, ∃ u w : R p T A, ι e • b j = u • toV p T x + w • toV p T y := by
    intro j
    obtain ⟨k, z, hz⟩ := exists_pow_smul_eq_toV (p := p) (b j)
    obtain ⟨a₁, c₁, h₁⟩ := hspan z
    have h₂ : ((p : ℚ_[p]) ^ (N + k)) • (ι e • b j) = ι a₁ • toV p T x + ι c₁ • toV p T y := by
      rw [hι_smul, hι_smul, ← map_add, ← h₁, toV_pow_smul, ← hι_smul, pow_add, mul_smul, smul_R_apply,
        smul_R_apply, ← map_smul (ι e : Module.End ℚ_[p] (V p T)) ((p : ℚ_[p]) ^ k) (b j), hz]
    have hpk : ((p : ℚ_[p]) ^ (N + k)) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    refine ⟨((p : ℚ_[p]) ^ (N + k))⁻¹ • ι a₁, ((p : ℚ_[p]) ^ (N + k))⁻¹ • ι c₁, ?_⟩
    rw [qsmul_R_smul, qsmul_R_smul, ← smul_add, ← h₂, smul_smul, inv_mul_cancel₀ hpk, one_smul]

  have hcol : ∀ (z : T) (a₀ c₀ : 𝕋), ((p : ℤ_[p]) ^ N) • ρ σ z = a₀ • x + c₀ • y →
      s • ρR A ρ hcomm σ (toV p T z) = ι a₀ • toV p T x + ι c₀ • toV p T y := by
    intro z a₀ c₀ h
    rw [hs, ρR_apply, baseChange_toV, ← toV_pow_smul, h, map_add, ← hι_smul, ← hι_smul]
  obtain ⟨h1, h2⟩ := idem_mul_trace_det_eq_of_span b (ρR A ρ hcomm σ) hε s (toV p T x) (toV p T y)
    hspanV (ι a) (ι b') (ι c) (ι d') (hcol x a c hx) (hcol y b' d' hy)
  simp only [ρR_apply] at h1 h2
  rw [← hιt, hsι, ← hι_add, ← hι_mul, ← hι_mul] at h1
  rw [← hιd, pow_two, mul_assoc, hsι, hsι, ← mul_assoc, ← pow_add, ← two_mul, ← hι_mul a d',
    ← hι_mul b' c, ← hι_sub, ← hι_mul, ← hι_mul] at h2
  exact ⟨hιinj h1, hιinj h2⟩

end Lattice

end Abstract

section Corner

variable {B : Type} [CommRing B] (S' : IharaLemma.IdempotentSplitting B) (i : Fin S'.n)

theorem toCornerRing_coe (z : S'.CornerRing i) : S'.toCornerRing i (z : B) = z :=
  Subtype.ext (by
    show S'.e i * (z : B) * S'.e i = z
    rw [S'.e_mul_coe, S'.coe_mul_e])

theorem toCornerRing_eq_of_e_mul_eq {u v : B} (h : S'.e i * u = S'.e i * v) :
    S'.toCornerRing i u = S'.toCornerRing i v :=
  Subtype.ext (by
    show S'.e i * u * S'.e i = S'.e i * v * S'.e i
    rw [h])

end Corner

section Final

variable {p : ℕ} [Fact p.Prime]
variable {T : Type} [AddCommGroup T] [Module ℤ_[p] T] [Module.Free ℤ_[p] T]
variable {M : ℕ} {S : Finset ℕ}
variable {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 T] [IsScalarTower ℤ_[p] 𝕋 T]

theorem final
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] T)
    (A : CohCarrier.Gen M (↑S : Set ℕ) → Module.End ℤ_[p] T)
    (hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M (↑S : Set ℕ))
      (x : T), ρ σ (A g x) = A g (ρ σ x))
    (b : Module.Basis (Fin 2) (R p T A) (V p T))
    (op : CohCarrier.Gen M (↑S : Set ℕ) → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M (↑S : Set ℕ)) (x : T), op g • x = A g x)
    (hfaith : ∀ t : 𝕋, (∀ x : T, t • x = 0) → t = 0)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (core : ∃ (t d : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → 𝕋)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),
      t 1 = 2 ∧ d 1 = 1 ∧
      (∀ σ τ, t (σ * τ * σ⁻¹) = t τ) ∧ (∀ σ τ, d (σ * τ * σ⁻¹) = d τ) ∧
      (∀ σ τ, d (σ * τ) = d σ * d τ) ∧
      (∀ σ, t σ * t σ = t (σ * σ) + 2 * d σ) ∧
      (∀ σ (x : T), ρ σ (ρ σ x) - t σ • ρ σ x + d σ • x = 0) ∧
      (∀ σ (u : 𝕋) (x : T), ρ σ (u • x) = u • ρ σ x) ∧
      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ c : 𝕋, t (σ * τ) = t τ + (p : 𝕋) ^ n * c) ∧
          (∀ τ, ∃ c : 𝕋, d (σ * τ) = d τ + (p : 𝕋) ^ n * c)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A'.IsFrobeniusAt σ ℓ →
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * t σ = op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ∧
            op (CohCarrier.Gen.dia (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))
                * d σ = (ℓ : 𝕋)) ∧
      (∀ σ, (Algebra.lsmul ℤ_[p] ℤ_[p] T (t σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 + b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1) ∧
          (Algebra.lsmul ℤ_[p] ℤ_[p] T (d σ)).baseChange ℚ_[p]
            = ↑(b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 1
                - b.repr ((ρ σ).baseChange ℚ_[p] (b 1)) 0 * b.repr ((ρ σ).baseChange ℚ_[p] (b 0)) 1)))
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n) :
    ∃ (tr dt : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),
      tr 1 = 2 ∧ dt 1 = 1 ∧
      (∀ σ τ, tr (σ * τ * σ⁻¹) = tr τ) ∧ (∀ σ τ, dt (σ * τ * σ⁻¹) = dt τ) ∧
      (∀ σ τ, dt (σ * τ) = dt σ * dt τ) ∧
      (∀ σ, tr σ * tr σ = tr (σ * σ) + 2 * dt σ) ∧
      (∀ σ, ∀ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀),
        ρ σ (ρ σ x) - ((tr σ : S'.CornerRing i₀) : 𝕋) • ρ σ x + ((dt σ : S'.CornerRing i₀) : 𝕋) • x = 0) ∧
      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : T, ∃ y : T, ρ σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, tr (σ * τ) = tr τ + (p : S'.CornerRing i₀) ^ n * b) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, dt (σ * τ) = dt τ + (p : S'.CornerRing i₀) ^ n * b)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            S'.toCornerRing i₀ (op (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) * tr σ =
              S'.toCornerRing i₀ (op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) ∧
            S'.toCornerRing i₀ (op (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) * dt σ =
              (ℓ : S'.CornerRing i₀)) ∧
      (∀ x ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀),
        ∀ y ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀),
          (∀ a b : S'.CornerRing i₀,
            ((a : S'.CornerRing i₀) : 𝕋) • x + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0) →
          ∀ N : ℕ,
            (∀ z ∈ IharaLemma.cornerSubmodule (M := T) (S'.e i₀),
              ∃ a b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z =
                ((a : S'.CornerRing i₀) : 𝕋) • x + ((b : S'.CornerRing i₀) : 𝕋) • y) →
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a b c d : S'.CornerRing i₀),
              ((p : ℤ_[p]) ^ N) • ρ σ x =
                ((a : S'.CornerRing i₀) : 𝕋) • x + ((c : S'.CornerRing i₀) : 𝕋) • y →
              ((p : ℤ_[p]) ^ N) • ρ σ y =
                ((b : S'.CornerRing i₀) : 𝕋) • x + ((d : S'.CornerRing i₀) : 𝕋) • y →
              (p : S'.CornerRing i₀) ^ N * tr σ = a + d ∧
              (p : S'.CornerRing i₀) ^ (2 * N) * dt σ = a * d - b * c) := by
  haveI := isMulCommutative_R A op hop
  obtain ⟨tt, dd, L, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hcoord⟩ := core
  set π := S'.toCornerRing i₀ with hπ
  refine ⟨fun σ => π (tt σ), fun σ => π (dd σ), L, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals beta_reduce
  · rw [h1, map_ofNat]
  · rw [h2, map_one]
  · intro σ τ; rw [h3]
  · intro σ τ; rw [h4]
  · intro σ τ; rw [h5, map_mul]
  · intro σ; rw [← map_mul, h6, map_add, map_mul, map_ofNat]
  ·
    intro σ x hx
    have hex : S'.e i₀ • x = x := S'.e_smul_coe i₀ ⟨x, hx⟩
    have hcoe_t : ((π (tt σ) : S'.CornerRing i₀) : 𝕋) = S'.e i₀ * tt σ * S'.e i₀ := rfl
    have hcoe_d : ((π (dd σ) : S'.CornerRing i₀) : 𝕋) = S'.e i₀ * dd σ * S'.e i₀ := rfl
    rw [hcoe_t, hcoe_d]
    have e1 : ρ σ (ρ σ x) = S'.e i₀ • ρ σ (ρ σ x) := by rw [← h8, ← h8, hex]
    have e2 : (S'.e i₀ * tt σ * S'.e i₀) • ρ σ x = S'.e i₀ • (tt σ • ρ σ x) := by
      rw [mul_smul, mul_smul, ← h8 σ (S'.e i₀) x, hex]
    have e3 : (S'.e i₀ * dd σ * S'.e i₀) • x = S'.e i₀ • (dd σ • x) := by
      rw [mul_smul, mul_smul, hex]
    rw [e2, e3, e1, ← smul_sub, ← smul_add, h7, smul_zero]
  ·
    intro n
    obtain ⟨hfin, hσ⟩ := h9 n
    refine ⟨hfin, fun σ hfix => ?_⟩
    obtain ⟨hx, htr, hdt'⟩ := hσ σ hfix
    refine ⟨hx, fun τ => ?_, fun τ => ?_⟩
    · obtain ⟨c, hc⟩ := htr τ
      exact ⟨π c, by rw [hc, map_add, map_mul, map_pow, map_natCast]⟩
    · obtain ⟨c, hc⟩ := hdt' τ
      exact ⟨π c, by rw [hc, map_add, map_mul, map_pow, map_natCast]⟩
  ·
    intro ℓ hℓ hℓS hℓM hℓp A' hA σ hσ
    obtain ⟨htr, hdt'⟩ := h10 ℓ hℓ hℓS hℓM hℓp A' hA σ hσ
    exact ⟨by rw [← map_mul, htr], by rw [← map_mul, hdt', map_natCast]⟩
  ·
    intro x _hx y _hy _hfree N hcorner σ a b' c d' hρx hρy
    have hspan : ∀ z : T, ∃ a₀ c₀ : 𝕋, ((p : ℤ_[p]) ^ N) • (S'.e i₀ • z) = a₀ • x + c₀ • y := by
      intro z
      obtain ⟨a₀, c₀, h⟩ := hcorner (S'.e i₀ • z) ⟨z, rfl⟩
      exact ⟨a₀, c₀, h⟩
    obtain ⟨htr, hdt'⟩ := lattice op hcomm b hop hgen hfaith σ (tt σ) (dd σ)
      (hcoord σ).1 (hcoord σ).2 (S'.idem i₀) x y N hspan (a : 𝕋) (b' : 𝕋) (c : 𝕋) (d' : 𝕋) hρx hρy
    constructor
    · have e1 : (p : S'.CornerRing i₀) ^ N * π (tt σ) = π ((p : 𝕋) ^ N * tt σ) := by
        rw [map_mul, map_pow, map_natCast]
      have e2 : a + d' = π ((a : 𝕋) + (d' : 𝕋)) := by
        rw [map_add, toCornerRing_coe, toCornerRing_coe]
      rw [e1, e2]
      exact toCornerRing_eq_of_e_mul_eq S' i₀ htr
    · have e1 : (p : S'.CornerRing i₀) ^ (2 * N) * π (dd σ) = π ((p : 𝕋) ^ (2 * N) * dd σ) := by
        rw [map_mul, map_pow, map_natCast]
      have e2 : a * d' - b' * c = π ((a : 𝕋) * (d' : 𝕋) - (b' : 𝕋) * (c : 𝕋)) := by
        rw [map_sub, map_mul, map_mul, toCornerRing_coe, toCornerRing_coe, toCornerRing_coe,
          toCornerRing_coe]
      rw [e1, e2]
      exact toCornerRing_eq_of_e_mul_eq S' i₀ hdt'

end Final

end TMatPkg

namespace TMatJH

p2m_open "ModularCurve~baseChangeHom"

variable (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)

theorem hcommJH (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M (↑S : Set ℕ))
    (x : TateModule p (JH M H)) :
    JH.tateGaloisRep M H p σ (tateGenOpH M H (↑S : Set ℕ) p g x)
      = tateGenOpH M H (↑S : Set ℕ) p g (JH.tateGaloisRep M H p σ x) :=
  Subtype.ext (funext fun n => galois_smul_genOpH_comm M H (↑S : Set ℕ) σ g ((x : ℕ → JH M H) n))

theorem level (j : ℕ) : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ∀ x : TateModule p (JH M H), ∃ y : TateModule p (JH M H),
        JH.tateGaloisRep M H p σ x = x + ((p : ℤ_[p]) ^ j) • y := by
  obtain ⟨L, hL, hfix⟩ := JH.exists_finiteDimensional_smul_eq_self_of_torsion M H (p ^ j)
    (pow_pos (Fact.out : p.Prime).pos j)
  refine ⟨L, hL, fun σ hσ x => ?_⟩
  have hproj : TateModule.proj p (JH M H) j (JH.tateGaloisRep M H p σ x - x) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hfix σ hσ _ (TateModule.torsion x j)
  refine ⟨TateModule.shiftOfProjEqZero j _ hproj, ?_⟩
  rw [TateModule.pow_smul_shiftOfProjEqZero, add_sub_cancel]

omit [NeZero M] in

theorem bijective_dia (u : (ZMod M)ˣ) :
    Function.Bijective (tateGenOpH M H (↑S : Set ℕ) p (CohCarrier.Gen.dia u)) := by
  let γ := AlgebraicCurve.SemilinearAut.ofAlgAut (diamondAutHBar M H u)
  let inv : Module.End ℤ_[p] (TateModule p (JH M H)) :=
    JH.tateEnd M H p (DistribSMul.toAddMonoidHom (JH M H) γ⁻¹)
  have h1 : ∀ x, inv (tateGenOpH M H (↑S : Set ℕ) p (CohCarrier.Gen.dia u) x) = x := fun x =>
    Subtype.ext (funext fun n => inv_smul_smul γ ((x : ℕ → JH M H) n))
  have h2 : ∀ x, tateGenOpH M H (↑S : Set ℕ) p (CohCarrier.Gen.dia u) (inv x) = x := fun x =>
    Subtype.ext (funext fun n => smul_inv_smul γ ((x : ℕ → JH M H) n))
  exact ⟨fun x y hxy => by rw [← h1 x, ← h1 y, hxy], fun y => ⟨inv y, h2 y⟩⟩

end TMatJH

theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M ↑S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H ↑S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n) :
    ∃ (tr dt : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → S'.CornerRing i₀)
      (L : ℕ → IntermediateField ℚ (AlgebraicClosure ℚ)),

      tr 1 = 2 ∧ dt 1 = 1 ∧

      (∀ σ τ, tr (σ * τ * σ⁻¹) = tr τ) ∧ (∀ σ τ, dt (σ * τ * σ⁻¹) = dt τ) ∧
      (∀ σ τ, dt (σ * τ) = dt σ * dt τ) ∧

      (∀ σ, tr σ * tr σ = tr (σ * σ) + 2 * dt σ) ∧
      (∀ σ, ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ModularCurve.JH.tateGaloisRep M H p σ (ModularCurve.JH.tateGaloisRep M H p σ x)
          - ((tr σ : S'.CornerRing i₀) : 𝕋) • ModularCurve.JH.tateGaloisRep M H p σ x
          + ((dt σ : S'.CornerRing i₀) : 𝕋) • x = 0) ∧

      (∀ n : ℕ, FiniteDimensional ℚ (L n) ∧
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L n, σ x = x) →
          (∀ x : TateModule p (ModularCurve.JH M H), ∃ y : TateModule p (ModularCurve.JH M H),
            ModularCurve.JH.tateGaloisRep M H p σ x = x + ((p : ℤ_[p]) ^ n) • y) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, tr (σ * τ) = tr τ + (p : S'.CornerRing i₀) ^ n * b) ∧
          (∀ τ, ∃ b : S'.CornerRing i₀, dt (σ * τ) = dt τ + (p : S'.CornerRing i₀) ^ n * b)) ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            S'.toCornerRing i₀ (op (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) * tr σ =
              S'.toCornerRing i₀ (op (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) ∧
            S'.toCornerRing i₀ (op (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) * dt σ =
              (ℓ : S'.CornerRing i₀)) ∧

      (∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ∀ y ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
          (∀ a b : S'.CornerRing i₀,
            ((a : S'.CornerRing i₀) : 𝕋) • x + ((b : S'.CornerRing i₀) : 𝕋) • y = 0 → a = 0 ∧ b = 0) →
          ∀ N : ℕ,
            (∀ z ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
              ∃ a b : S'.CornerRing i₀, ((p : ℤ_[p]) ^ N) • z =
                ((a : S'.CornerRing i₀) : 𝕋) • x + ((b : S'.CornerRing i₀) : 𝕋) • y) →
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a b c d : S'.CornerRing i₀),
              ((p : ℤ_[p]) ^ N) • ModularCurve.JH.tateGaloisRep M H p σ x =
                ((a : S'.CornerRing i₀) : 𝕋) • x + ((c : S'.CornerRing i₀) : 𝕋) • y →
              ((p : ℤ_[p]) ^ N) • ModularCurve.JH.tateGaloisRep M H p σ y =
                ((b : S'.CornerRing i₀) : 𝕋) • x + ((d : S'.CornerRing i₀) : 𝕋) • y →
              (p : S'.CornerRing i₀) ^ N * tr σ = a + d ∧
              (p : S'.CornerRing i₀) ^ (2 * N) * dt σ = a * d - b * c) := by
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
    (ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH M p H).1
  haveI : Module.Free ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
    (ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH M p H).2
  exact TMatPkg.final (T := TateModule p (ModularCurve.JH M H))
    (ModularCurve.JH.tateGaloisRep M H p) (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)
    (TMatJH.hcommJH M p H S)
    (Classical.choice (ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH M p H S hin))
    op hop hfaith hgen
    (GaloisLattice.exists_trace_det_of_basis_fin_two_of_frobenius_relations p
      (TateModule p (ModularCurve.JH M H)) M S
      (ModularCurve.JH.tateGaloisRep M H p) (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p)
      (TMatJH.hcommJH M p H S) (TMatJH.bijective_dia M p H S) (TMatJH.level M p H)
      (Classical.choice (ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH M p H S hin))
      (fun ℓ hℓ hℓS hℓM hℓp A' hA σ hσ x =>
        ModularCurve.frobeniusQuadratic_tateModule_jH M p H (↑S : Set ℕ) hin hℓ hℓS hℓM hℓp A' hA σ hσ x)
      (fun ℓ hℓ hℓS hℓM hℓp A' hA σ hσ =>
        ModularCurve.diamond_mul_coordDet_eq_of_basis_rationalTateModule_jH M p H S hin
          (Classical.choice (ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH M p H S hin))
          hℓ hℓS hℓM hℓp A' hA σ hσ)
      hfaith op hop hgen)
    S' i₀

end S_ModularCurve_exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH
end P2MW
export P2MW.S_ModularCurve_exists_trace_det_latticeMatrix_tateGaloisRep_cornerSubmodule_tateModule_jH (solution)
