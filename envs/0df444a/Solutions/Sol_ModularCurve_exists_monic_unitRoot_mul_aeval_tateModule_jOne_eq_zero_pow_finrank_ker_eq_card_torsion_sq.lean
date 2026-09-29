-- Prove2me | solution 1 for ModularCurve.exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2cdc7611-dde8-59e1-9144-840b1fe4da84

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq
import Theorems.Thm_ModularCurve_natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
import Theorems.Thm_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ExtCitation.archimedeanLoc_archimedeanGen"
p2m_attr_erase "simp" "complexConjAlgEquiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Polynomial

noncomputable section

namespace G1UnitRootCount

section KerFactor

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem coe_aeval_restrict_apply (F : Module.End K W) {V : Submodule K W} (hV : ∀ x ∈ V, F x ∈ V)
    (r : K[X]) (w : V) : ((aeval (F.restrict hV) r w : V) : W) = aeval F r (w : W) := by
  induction r using Polynomial.induction_on' with
  | add r s hr hs => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hr, hs]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.End.pow_restrict, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, LinearMap.restrict_apply]

theorem aeval_eq_zero_of_isRoot_charpoly (L : Type*) [Field L] [Algebra K L]
    {W₁ : Type*} [AddCommGroup W₁] [Module K W₁] [FiniteDimensional K W₁]
    (F₁ : Module.End K W₁) (P : K[X]) (hF₁ : aeval F₁ P = 0)
    (a : L) (ha : aeval a F₁.charpoly = 0) : aeval a P = 0 := by
  set G : Module.End L (TensorProduct K L W₁) := F₁.baseChange L with hG
  have hchar : G.charpoly = F₁.charpoly.map (algebraMap K L) := LinearMap.charpoly_baseChange F₁ L
  have hroot : G.charpoly.IsRoot a := by
    rw [hchar, IsRoot.def, eval_map, ← aeval_def, ha]
  have hev : G.HasEigenvalue a := (Module.End.hasEigenvalue_iff_isRoot_charpoly G a).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hGP : aeval G (P.map (algebraMap K L)) = 0 := by
    have h1 : aeval G P = 0 := by
      have key : (Module.End.baseChangeHom K L W₁) (aeval F₁ P) = aeval G P := by
        rw [hG, ← aeval_algHom_apply]
        rfl
      rw [hF₁, map_zero] at key
      exact key.symm
    rwa [aeval_map_algebraMap]
  have h2 := Module.End.aeval_apply_of_hasEigenvector (p := P.map (algebraMap K L)) hv
  rw [hGP, LinearMap.zero_apply, eval_map, ← aeval_def] at h2
  rcases smul_eq_zero.mp h2.symm with h | h
  · exact h
  · exact absurd h hv.2

theorem finrank_ker_aeval_eq_natDegree (F : Module.End K W) {P R : K[X]} (hP : P.Monic)
    (hR : R.Monic) (hPR : IsCoprime P R) (hchar : F.charpoly = P * R) :
    Module.finrank K ↥(LinearMap.ker (aeval F P)) = P.natDegree := by
  classical
  set W₁ := LinearMap.ker (aeval F P) with hW₁
  set W₂ := LinearMap.ker (aeval F R) with hW₂

  have hsup : W₁ ⊔ W₂ = ⊤ := by
    rw [hW₁, hW₂, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime F hPR, ← hchar,
      LinearMap.aeval_self_charpoly, LinearMap.ker_zero]
  have hdisj : Disjoint W₁ W₂ := Polynomial.disjoint_ker_aeval_of_isCoprime F hPR
  have hcompl : IsCompl W₁ W₂ := ⟨hdisj, codisjoint_iff.mpr hsup⟩

  have hcomm : ∀ r : K[X], aeval F r * F = F * aeval F r := by
    intro r
    have h1 : aeval F (r * X) = aeval F (X * r) := by rw [mul_comm]
    rw [map_mul, map_mul, aeval_X] at h1
    exact h1
  have hinv : ∀ (r : K[X]) (x : W), x ∈ LinearMap.ker (aeval F r) →
      F x ∈ LinearMap.ker (aeval F r) := by
    intro r x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hx, map_zero]
  have hW₁inv : ∀ x ∈ W₁, F x ∈ W₁ := hinv P
  have hW₂inv : ∀ x ∈ W₂, F x ∈ W₂ := hinv R
  set F₁ := F.restrict hW₁inv with hF₁
  set F₂ := F.restrict hW₂inv with hF₂

  set e := Submodule.prodEquivOfIsCompl W₁ W₂ hcompl with he
  have hψ : F₁.prodMap F₂ = e.symm.conj F := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.eq_symm_apply]
    rw [LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl',
      map_add]
    rfl
  have hchar' : F.charpoly = F₁.charpoly * F₂.charpoly := by
    rw [← e.symm.charpoly_conj F, ← hψ, LinearMap.charpoly_prodMap]

  have hF₁P : aeval F₁ P = 0 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [coe_aeval_restrict_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact w.2
  have hF₂R : aeval F₂ R = 0 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [coe_aeval_restrict_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact w.2

  set L := AlgebraicClosure K
  have hPR_root : ∀ a : L, aeval a P = 0 → aeval a R = 0 → False := by
    intro a hPa hRa
    obtain ⟨u, v, huv⟩ := hPR
    have := congrArg (aeval a) huv
    rw [map_add, map_mul, map_mul, hPa, hRa, mul_zero, mul_zero, add_zero, map_one] at this
    exact zero_ne_one this
  have hcop₁ : IsCoprime F₁.charpoly R := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K L]
    intro a
    by_contra h
    push Not at h
    exact hPR_root a (aeval_eq_zero_of_isRoot_charpoly L F₁ P hF₁P a h.1) h.2
  have hcop₂ : IsCoprime F₂.charpoly P := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K L]
    intro a
    by_contra h
    push Not at h
    exact hPR_root a h.2 (aeval_eq_zero_of_isRoot_charpoly L F₂ R hF₂R a h.1)

  have hc : F₁.charpoly * F₂.charpoly = P * R := hchar'.symm.trans hchar
  have hd₁ : F₁.charpoly.natDegree ≤ P.natDegree := by
    refine Polynomial.natDegree_le_of_dvd ?_ hP.ne_zero
    exact hcop₁.dvd_of_dvd_mul_right ⟨F₂.charpoly, hc.symm⟩
  have hd₂ : F₂.charpoly.natDegree ≤ R.natDegree := by
    refine Polynomial.natDegree_le_of_dvd ?_ hR.ne_zero
    refine hcop₂.dvd_of_dvd_mul_right ⟨F₁.charpoly, ?_⟩
    rw [mul_comm R P, ← hc, mul_comm]
  have hsum : F₁.charpoly.natDegree + F₂.charpoly.natDegree = P.natDegree + R.natDegree := by
    rw [← (LinearMap.charpoly_monic F₁).natDegree_mul (LinearMap.charpoly_monic F₂), hc,
      hP.natDegree_mul hR]
  have h₁ : F₁.charpoly.natDegree = P.natDegree := by omega
  rw [← h₁, LinearMap.charpoly_natDegree]

end KerFactor

section Hensel

variable {p : ℕ} [Fact p.Prime]

theorem exists_unitRoot_mul_eq_map (Q : ℤ[X]) (hQ : Q.Monic) :
    ∃ Qu Qn : ℤ_[p][X], Qu.Monic ∧ Qn.Monic ∧ IsUnit (Qu.coeff 0) ∧
      Qn.map (PadicInt.toZMod (p := p)) = X ^ Qn.natDegree ∧ IsCoprime Qu Qn ∧
      Qu * Qn = Q.map (algebraMap ℤ ℤ_[p]) ∧
      Qn.natDegree = (Q.map (Int.castRingHom (ZMod p))).natTrailingDegree := by
  set π := PadicInt.toZMod (p := p) with hπ
  set Qp := Q.map (algebraMap ℤ ℤ_[p]) with hQp
  set Qb := Q.map (Int.castRingHom (ZMod p)) with hQb
  have hQpm : Qp.Monic := hQ.map _
  have hQb_eq : Qp.map π = Qb := by
    rw [hQp, Polynomial.map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hQb : Qb.Monic := hQ.map _
  have hQb0 : Qb ≠ 0 := hQb.ne_zero

  set e := Qb.natTrailingDegree with he
  have hXdvd : X ^ e ∣ Qb := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  obtain ⟨R, hR⟩ := hXdvd
  have hR0 : R.coeff 0 ≠ 0 := by
    have h1 : Qb.coeff e = R.coeff 0 := by
      rw [hR, mul_comm, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self]
    rw [← h1]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hQb0
  have hRmonic : R.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_pow e) (hR ▸ hQb)
  have hcop₀ : IsCoprime (X ^ e : (ZMod p)[X]) R := by
    refine IsCoprime.pow_left ?_
    rw [Irreducible.coprime_iff_not_dvd Polynomial.irreducible_X, Polynomial.X_dvd_iff]
    exact hR0

  haveI : IsAdicComplete (RingHom.ker π) ℤ_[p] := by
    rw [hπ, PadicInt.ker_toZMod]; infer_instance
  have hπsurj : Function.Surjective π := ZMod.ringHom_surjective π
  obtain ⟨g, h, hg, hh, hgh, hgmap, hhmap, hcop, -⟩ :=
    Polynomial.exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete π hπsurj hQpm
      (monic_X_pow e) hRmonic hcop₀ (hQb_eq.trans hR)

  have hgdeg : g.natDegree = e := by
    rw [← hg.natDegree_map π, hgmap, natDegree_X_pow]
  refine ⟨h, g, hh, hg, ?_, ?_, hcop.symm, ?_, hgdeg⟩
  ·
    have h0 : π (h.coeff 0) ≠ 0 := by
      rw [← Polynomial.coeff_map, hhmap]; exact hR0
    have hnot : h.coeff 0 ∉ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h0
    by_contra hu
    exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  · rw [hgmap, hgdeg]
  · rw [mul_comm, hgh]

end Hensel

section TateFree

variable (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A]

theorem noZeroSMulDivisors_tateModule : NoZeroSMulDivisors ℤ_[p] (TateModule p A) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  set v : ℕ := a.valuation with hv
  set u : ℤ_[p]ˣ := PadicInt.unitCoeff ha with hu
  have hspec : a = (u : ℤ_[p]) * (p : ℤ_[p]) ^ v := PadicInt.unitCoeff_spec ha
  have hpv : ((p : ℤ_[p]) ^ v) • x = 0 := by
    have h1 : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • (a • x) = 0 := by rw [h, smul_zero]
    have h2 : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * a = (p : ℤ_[p]) ^ v := by
      rw [hspec, ← mul_assoc, Units.inv_mul, one_mul]
    rw [smul_smul, h2] at h1
    exact h1
  refine Subtype.ext (funext fun n => ?_)
  have hlevel : (((((p : ℤ_[p]) ^ v) • x : TateModule p A)) : ℕ → A) (n + v) = 0 := by
    rw [hpv]; rfl
  rw [← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply, TateModule.compat_pow x n v] at hlevel
  exact hlevel

theorem free_tateModule [Module.Finite ℤ_[p] (TateModule p A)] : Module.Free ℤ_[p] (TateModule p A) := by
  haveI := noZeroSMulDivisors_tateModule p A
  exact Module.free_of_finite_type_torsion_free'

end TateFree

section Assembly

open scoped TensorProduct

variable {p : ℕ} [Fact p.Prime]

theorem main_generic {T : Type*} [AddCommGroup T] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T]
    [Module.Free ℤ_[p] T] (F : Module.End ℤ_[p] T) (Q : ℤ[X]) (hQ : Q.Monic)
    (hchar : F.charpoly = (Q ^ 2).map (algebraMap ℤ ℤ_[p]))
    (c : ℕ) (hc : c = p ^ (Q.natDegree - (Q.map (Int.castRingHom (ZMod p))).natTrailingDegree))
    (K : Type*) [Field K] [Algebra ℤ_[p] K] :
    ∃ Pu Pn : Polynomial ℤ_[p], Pu.Monic ∧ Pn.Monic ∧ IsUnit (Pu.coeff 0) ∧
      Pn.map (PadicInt.toZMod (p := p)) = Polynomial.X ^ Pn.natDegree ∧
      Polynomial.aeval (F.baseChange K) ((Pu * Pn).map (algebraMap ℤ_[p] K)) = 0 ∧
      p ^ Module.finrank K
          ↥(LinearMap.ker (Polynomial.aeval (F.baseChange K) (Pu.map (algebraMap ℤ_[p] K)))) = c ^ 2 := by
  classical

  obtain ⟨Qu, Qn, hQu, hQn, hunit, hQnX, hcop, hprod, hdeg⟩ := exists_unitRoot_mul_eq_map (p := p) Q hQ
  set ι : ℤ_[p] →+* K := algebraMap ℤ_[p] K with hι
  set FK : Module.End K (K ⊗[ℤ_[p]] T) := F.baseChange K with hFK

  have hcharK : FK.charpoly = (Qu ^ 2).map ι * (Qn ^ 2).map ι := by
    rw [hFK, LinearMap.charpoly_baseChange, hchar, Polynomial.map_pow, ← hprod]
    simp only [Polynomial.map_pow, Polynomial.map_mul]
    ring

  have hdegQu : Qu.natDegree = Q.natDegree - (Q.map (Int.castRingHom (ZMod p))).natTrailingDegree := by
    have hsum : Qu.natDegree + Qn.natDegree = Q.natDegree := by
      rw [← hQu.natDegree_mul hQn, hprod, hQ.natDegree_map]
    omega
  refine ⟨Qu ^ 2, Qn ^ 2, hQu.pow 2, hQn.pow 2, ?_, ?_, ?_, ?_⟩
  ·
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, ← Polynomial.coeff_zero_eq_eval_zero]
    exact hunit.pow 2
  ·
    rw [Polynomial.map_pow, hQnX, ← pow_mul, hQn.natDegree_pow, mul_comm]
  ·
    have : (Qu ^ 2 * Qn ^ 2).map ι = FK.charpoly := by
      rw [hcharK, Polynomial.map_mul]
    rw [this]
    exact LinearMap.aeval_self_charpoly FK
  ·
    have hcopK : IsCoprime ((Qu ^ 2).map ι) ((Qn ^ 2).map ι) := by
      have h := (hcop.pow (m := 2) (n := 2)).map (Polynomial.mapRingHom ι)
      rwa [Polynomial.coe_mapRingHom] at h
    have hker : Module.finrank K ↥(LinearMap.ker (aeval FK ((Qu ^ 2).map ι))) = 2 * Qu.natDegree := by
      rw [finrank_ker_aeval_eq_natDegree FK ((hQu.pow 2).map ι) ((hQn.pow 2).map ι) hcopK hcharK,
        (hQu.pow 2).natDegree_map, hQu.natDegree_pow, mul_comm]
    rw [hker, hc, ← hdegQu, ← pow_mul, mul_comm]

end Assembly

end G1UnitRootCount

end

open G1UnitRootCount in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ Pu Pn : Polynomial ℤ_[p], Pu.Monic ∧ Pn.Monic ∧ IsUnit (Pu.coeff 0) ∧
        Pn.map (PadicInt.toZMod (p := p)) = Polynomial.X ^ Pn.natDegree ∧
        Polynomial.aeval
            ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
              (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K)
            ((Pu * Pn).map (algebraMap ℤ_[p] K)) = 0 ∧
        p ^ Module.finrank K
            ↥(LinearMap.ker (Polynomial.aeval
              ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M)
                (ModularCurve.heckeGenOne ⟨p, Fact.out⟩)).baseChange K)
              (Pu.map (algebraMap ℤ_[p] K)))) =
          (Nat.card {y : ModularCurve.JOneC M (IsLocalRing.ResidueField P) // p • y = 0}) ^ 2 := by
  intro P hP
  have hp : p.Prime := Fact.out

  haveI : IsAlgClosed (IsLocalRing.ResidueField P) := ValuationSubring.isAlgClosed_residueField P
  haveI : CharP (IsLocalRing.ResidueField P) p :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hp hP

  obtain ⟨n, b, -⟩ := CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast M
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) := Module.Finite.of_basis b

  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M p
  haveI : Module.Free ℤ_[p] (TateModule p (ModularCurve.JOne M)) := free_tateModule p (ModularCurve.JOne M)

  obtain ⟨Q, hQm, hQC, hchar⟩ :=
    ModularCurve.exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq
      M p hp hpM

  have hcard :=
    ModularCurve.natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne
      M p hpM (IsLocalRing.ResidueField P) Q hQC
  exact main_generic _ Q hQm hchar _ hcard K

end S_ModularCurve_exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq
end P2MW
export P2MW.S_ModularCurve_exists_monic_unitRoot_mul_aeval_tateModule_jOne_eq_zero_pow_finrank_ker_eq_card_torsion_sq (solution)
