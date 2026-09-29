-- Prove2me | solution 1 for ModularCurve.exists_irreducible_isCoprime_eq_mul_pow_of_coe_eq_hasseRootFn_pow_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c59623b0-c428-5518-a255-1b795584a79e

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_ModularCurve_gcd_sub_one_natAbs_ord_eq_one_of_evalAt_mem_ssJSet_of_coe_eq_hasseRootFn_pow
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_isRational_place_x1FunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_irreducible_isCoprime_eq_mul_pow_of_coe_eq_hasseRootFn_pow_of_mem_ssJSet
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one"
p2m_attr_erase "simp" "compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false

p2m_open "ModularCurve~coeffMap_jqModC AlgebraicCurve"

noncomputable section

namespace B3E100

section coeff

variable {κ κ' : Type*} [Field κ] [Field κ']

theorem coeffMap_intSeriesC (σ : κ →+* κ') (s : PowerSeries ℤ) :
    coeffMap σ (intSeriesC κ s) = intSeriesC κ' s := by
  change (HahnSeries.ofPowerSeries ℤ κ (s.map (Int.castRingHom κ))).map σ =
    HahnSeries.ofPowerSeries ℤ κ' (s.map (Int.castRingHom κ'))
  ext k
  rw [HahnSeries.map_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_map]
    simp
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem coeffMap_jqModC (σ : κ →+* κ') : coeffMap σ (jqModC κ) = jqModC κ' :=
  map_jqModC σ

theorem coeffMap_algebraMap' (σ : κ →+* κ') (c : κ) :
    coeffMap σ (algebraMap κ (LaurentSeries κ) c) = algebraMap κ' (LaurentSeries κ') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

def IntegralWeightOneForm.changeCoeff (σ : κ →+* κ') {M : ℕ} (w : IntegralWeightOneForm κ M) :
    IntegralWeightOneForm κ' M where
  form := w.form
  series := w.series
  isIntegralQExp := w.isIntegralQExp
  intSeriesC_ne_zero := by
    rw [← coeffMap_intSeriesC σ]
    exact (map_ne_zero_iff _ (coeffMap σ).injective).mpr w.intSeriesC_ne_zero

theorem IntegralWeightOneForm.hasseRootFn_changeCoeff (σ : κ →+* κ') {M : ℕ}
    (w : IntegralWeightOneForm κ M) :
    (IntegralWeightOneForm.changeCoeff σ w).hasseRootFn = coeffMap σ w.hasseRootFn := by
  change (intSeriesC κ' w.series)⁻¹ = coeffMap σ (intSeriesC κ w.series)⁻¹
  rw [map_inv₀, coeffMap_intSeriesC]

theorem intFormRatiosC_subset_image (σ : κ →+* κ') (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    intFormRatiosC κ' Γ ⊆ coeffMap σ '' intFormRatiosC κ Γ := by
  rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have hg0' : intSeriesC κ pg ≠ 0 := by
    intro h
    apply hg0
    rw [← coeffMap_intSeriesC σ, h, map_zero]
  refine ⟨intSeriesC κ pf / intSeriesC κ pg, ⟨k, f, g, pf, pg, hf, hg, hg0', rfl⟩, ?_⟩
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

end coeff

theorem cf_package (p : ℕ) [Fact p.Prime] (κ κ' : Type) [Field κ] [Field κ'] [CharP κ p]
    [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] (M : ℕ) [NeZero M] (w : IntegralWeightOneForm κ M)
    (jbar : ↥(x1FunctionFieldC κ M)) (hjbar : (jbar : LaurentSeries κ) = jqModC κ) :
    ∃ (ι : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC κ' M)) (w' : IntegralWeightOneForm κ' M),
      (∀ x, ((ι x : ↥(x1FunctionFieldC κ' M)) : LaurentSeries κ') = coeffMap (algebraMap κ κ') (x : LaurentSeries κ)) ∧
      (∀ c : κ, ι (algebraMap κ ↥(x1FunctionFieldC κ M) c) = algebraMap κ' ↥(x1FunctionFieldC κ' M) (algebraMap κ κ' c)) ∧
      ((ι jbar : ↥(x1FunctionFieldC κ' M)) : LaurentSeries κ') = jqModC κ' ∧
      w'.hasseRootFn = coeffMap (algebraMap κ κ') w.hasseRootFn ∧
      (letI := ι.toAlgebra; Algebra.adjoin ↥(x1FunctionFieldC κ M)
        (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) = ⊤) := by
  set σ : κ →+* κ' := algebraMap κ κ' with hσ
  obtain ⟨ι, hι⟩ :
      ∃ ι : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC κ' M), ∀ x : ↥(x1FunctionFieldC κ M), ((ι x : ↥(x1FunctionFieldC κ' M)) : LaurentSeries κ') = coeffMap σ (x : LaurentSeries κ) :=
    exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap σ (CongruenceSubgroup.Gamma1 M)
  have hconst : ∀ c : κ, ι (algebraMap κ ↥(x1FunctionFieldC κ M) c) = algebraMap κ' ↥(x1FunctionFieldC κ' M) (σ c) := by
    intro c
    apply Subtype.ext
    rw [hι]
    change coeffMap σ (algebraMap κ (LaurentSeries κ) c) = algebraMap κ' (LaurentSeries κ') (σ c)
    exact coeffMap_algebraMap' σ c
  have hj : ((ι jbar : ↥(x1FunctionFieldC κ' M)) : LaurentSeries κ') = jqModC κ' := by
    rw [hι, hjbar, coeffMap_jqModC]
  refine ⟨ι, IntegralWeightOneForm.changeCoeff σ w, hι, hconst, hj,
    IntegralWeightOneForm.hasseRootFn_changeCoeff σ w, ?_⟩
  letI instA : Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) := ι.toAlgebra

  have halg : ∀ y ∈ Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M)), IsAlgebraic ↥(x1FunctionFieldC κ M) y := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨f, hf0, hf⟩ := Algebra.IsAlgebraic.isAlgebraic (R := κ) c
    refine ⟨f.map (algebraMap κ ↥(x1FunctionFieldC κ M)), (Polynomial.map_ne_zero_iff (algebraMap κ ↥(x1FunctionFieldC κ M)).injective).mpr hf0, ?_⟩
    have hcomp : (algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M)).comp (algebraMap κ ↥(x1FunctionFieldC κ M)) = (algebraMap κ' ↥(x1FunctionFieldC κ' M)).comp σ :=
      RingHom.ext fun c => hconst c
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      hf, map_zero]

  have hadj : IntermediateField.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M))) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hsub : Set.range (algebraMap κ' (LaurentSeries κ')) ∪ intFormRatiosC κ' (CongruenceSubgroup.Gamma1 M) ⊆
        ((IntermediateField.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M)))).toSubfield.map
          (x1FunctionFieldC κ' M).val.toRingHom : Set (LaurentSeries κ')) := by
      rintro y (⟨c, rfl⟩ | hy)
      · exact Subfield.mem_map.mpr
          ⟨algebraMap κ' ↥(x1FunctionFieldC κ' M) c, IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩, rfl⟩
      · obtain ⟨z, hz, rfl⟩ := intFormRatiosC_subset_image σ _ hy
        have hzK : z ∈ x1FunctionFieldC κ M := intFormRatiosC_subset κ _ hz
        refine Subfield.mem_map.mpr ⟨ι ⟨z, hzK⟩, ?_, ?_⟩
        · exact IntermediateField.algebraMap_mem
            (IntermediateField.adjoin ↥(x1FunctionFieldC κ M) (Set.range (algebraMap κ' ↥(x1FunctionFieldC κ' M)))) ⟨z, hzK⟩
        · exact hι ⟨z, hzK⟩
    have hx2 : (x : LaurentSeries κ') ∈ Subfield.closure
        (Set.range (algebraMap κ' (LaurentSeries κ')) ∪ intFormRatiosC κ' (CongruenceSubgroup.Gamma1 M)) :=
      x.2
    obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (Subfield.closure_le.mpr hsub hx2)
    have hyx' : y = x := Subtype.ext hyx
    exact hyx' ▸ hy
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, hadj,
    IntermediateField.top_toSubalgebra]

section valext

variable {F F' : Type*} [Field F] [Field F']

theorem ofPrime_eq_self_of_eq (O : ValuationSubring F) (P : Ideal ↥O) [P.IsPrime]
    (hP : P = IsLocalRing.maximalIdeal ↥O) : ValuationSubring.ofPrime O P = O := by
  subst hP
  exact ValuationSubring.ofPrime_top O

theorem valuationSubring_eq_of_le_of_nonunits (O O₂ : ValuationSubring F) (h : O ≤ O₂)
    (hloc : ∀ x : ↥O, (x : F) ∈ O.nonunits → (x : F) ∈ O₂.nonunits) : O₂ = O := by
  have hI : ValuationSubring.idealOfLE O O₂ h = IsLocalRing.maximalIdeal ↥O := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
    · intro x hx
      have hx' : (x : F) ∈ O.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hx
      obtain ⟨hmem, hy⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (hloc x hx')
      change x ∈ (IsLocalRing.maximalIdeal ↥O₂).comap (O.inclusion O₂ h)
      rw [Ideal.mem_comap]
      exact hy
  calc O₂ = ValuationSubring.ofPrime O (ValuationSubring.idealOfLE O O₂ h) :=
        (ValuationSubring.ofPrime_idealOfLE O O₂ h).symm
    _ = O := ofPrime_eq_self_of_eq O _ hI

theorem exists_valuationSubring_comap_eq (ι : F →+* F') (O : ValuationSubring F) :
    ∃ B : ValuationSubring F', B.comap ι = O ∧
      ∀ x : ↥O, (x : F) ∈ O.nonunits → ι (x : F) ∈ B.nonunits := by
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing (ι.comp O.subtype)

  have hunit : ∀ x : ↥O, IsUnit (⟨ι (x : F), hA x⟩ : ↥A) → IsUnit x := by
    intro x hu
    exact (hloc.map_nonunit x) hu
  have key : ∀ x : ↥O, (x : F) ∈ O.nonunits → ι (x : F) ∈ A.nonunits := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨hA x, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hunit x hu
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    exact hx this
  refine ⟨A, ?_, key⟩
  have hle : O ≤ A.comap ι := fun x hx => hA ⟨x, hx⟩
  refine valuationSubring_eq_of_le_of_nonunits O (A.comap ι) hle ?_
  intro x hx
  have h1 := key x hx
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at h1 ⊢
  obtain ⟨hmemA, hmax⟩ := h1
  refine ⟨hle x.2, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax ⊢
  intro hu
  apply hmax

  let g : ↥(A.comap ι) →+* ↥A :=
    (ι.comp (A.comap ι).subtype).codRestrict A.toSubring (fun y => y.2)
  have := hu.map g
  convert this <;> rfl

end valext

section resmap

variable {F F' : Type*} [Field F] [Field F']

def mapOfComapEq (ι : F →+* F') (O : ValuationSubring F) (B : ValuationSubring F')
    (hBO : B.comap ι = O) : ↥O →+* ↥B where
  toFun x := ⟨ι (x : F), ValuationSubring.mem_comap.mp (by rw [hBO]; exact x.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp]
theorem coe_mapOfComapEq (ι : F →+* F') (O : ValuationSubring F) (B : ValuationSubring F')
    (hBO : B.comap ι = O) (x : ↥O) :
    ((mapOfComapEq ι O B hBO x : ↥B) : F') = ι (x : F) := rfl

theorem ker_residue_comp_mapOfComapEq (ι : F →+* F') (O : ValuationSubring F)
    (B : ValuationSubring F') (hBO : B.comap ι = O)
    (hloc : ∀ x : ↥O, (x : F) ∈ O.nonunits → ι (x : F) ∈ B.nonunits) :
    RingHom.ker ((IsLocalRing.residue ↥B).comp (mapOfComapEq ι O B hBO)) =
      IsLocalRing.maximalIdeal ↥O := by
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
  constructor
  · intro hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact ((IsLocalRing.mem_maximalIdeal _).mp hx) (hu.map (mapOfComapEq ι O B hBO))
  · intro hx
    have h1 : (x : F) ∈ O.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hx
    have h2 : ((mapOfComapEq ι O B hBO x : ↥B) : F') ∈ B.nonunits := hloc x h1
    exact ValuationSubring.coe_mem_nonunits_iff.mp h2

end resmap

section rational

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k' F']

noncomputable def resEquiv (W : AlgebraicCurve.Place k' F') (hW : W.IsRational) :
    W.ResidueField ≃+* k' :=
  (RingEquiv.ofBijective (algebraMap k' W.ResidueField)
    ⟨W.algebraMap_residueField_injective, hW⟩).symm

theorem algebraMap_resEquiv (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (x : W.ResidueField) : algebraMap k' W.ResidueField (resEquiv W hW x) = x :=
  (RingEquiv.ofBijective (algebraMap k' W.ResidueField)
    ⟨W.algebraMap_residueField_injective, hW⟩).apply_symm_apply x

theorem resEquiv_algebraMap (W : AlgebraicCurve.Place k' F') (hW : W.IsRational) (c : k') :
    resEquiv W hW (algebraMap k' W.ResidueField c) = c :=
  (RingEquiv.ofBijective (algebraMap k' W.ResidueField)
    ⟨W.algebraMap_residueField_injective, hW⟩).symm_apply_apply c

theorem evalAt_eq_resEquiv_residue (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    {f : F'} (hf : f ∈ W.toValuationSubring) :
    W.evalAt f = resEquiv W hW (IsLocalRing.residue ↥W.toValuationSubring ⟨f, hf⟩) := by
  apply W.algebraMap_residueField_injective
  rw [W.algebraMap_evalAt hW hf, algebraMap_resEquiv]

end rational

section package

variable {F F' k' : Type*} [Field F] [Field F'] [Field k'] [Algebra k' F']

noncomputable def resHom (ι : F →+* F') (O : ValuationSubring F)
    (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (hBO : W.toValuationSubring.comap ι = O) : ↥O →+* k' :=
  ((resEquiv W hW).toRingHom.comp (IsLocalRing.residue ↥W.toValuationSubring)).comp
    (mapOfComapEq ι O W.toValuationSubring hBO)

theorem resHom_apply (ι : F →+* F') (O : ValuationSubring F)
    (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (hBO : W.toValuationSubring.comap ι = O) (f : ↥O) :
    resHom ι O W hW hBO f =
      resEquiv W hW (IsLocalRing.residue ↥W.toValuationSubring
        (mapOfComapEq ι O W.toValuationSubring hBO f)) := rfl

theorem ker_resHom (ι : F →+* F') (O : ValuationSubring F)
    (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (hBO : W.toValuationSubring.comap ι = O)
    (hloc : ∀ x : ↥O, (x : F) ∈ O.nonunits → ι (x : F) ∈ W.toValuationSubring.nonunits) :
    RingHom.ker (resHom ι O W hW hBO) = IsLocalRing.maximalIdeal ↥O := by
  rw [← ker_residue_comp_mapOfComapEq ι O W.toValuationSubring hBO hloc]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, resHom_apply, RingHom.comp_apply,
    map_eq_zero_iff _ (resEquiv W hW).injective]

theorem evalAt_eq_resHom (ι : F →+* F') (O : ValuationSubring F)
    (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (hBO : W.toValuationSubring.comap ι = O) (f : ↥O) :
    W.evalAt (ι (f : F)) = resHom ι O W hW hBO f := by
  have hf : ι (f : F) ∈ W.toValuationSubring :=
    ValuationSubring.mem_comap.mp (by rw [hBO]; exact f.2)
  rw [evalAt_eq_resEquiv_residue W hW hf, resHom_apply]
  rfl

theorem evalAt_eq_resHom' (ι : F →+* F') (O : ValuationSubring F)
    (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (hBO : W.toValuationSubring.comap ι = O) (f : F) (hf : f ∈ O) :
    W.evalAt (ι f) = resHom ι O W hW hBO ⟨f, hf⟩ :=
  evalAt_eq_resHom ι O W hW hBO ⟨f, hf⟩

theorem exists_ringHom_ker_eq_and_evalAt_eq (ι : F →+* F') (O : ValuationSubring F)
    (W : AlgebraicCurve.Place k' F') (hW : W.IsRational)
    (hBO : W.toValuationSubring.comap ι = O)
    (hloc : ∀ x : ↥O, (x : F) ∈ O.nonunits → ι (x : F) ∈ W.toValuationSubring.nonunits) :
    ∃ φ : ↥O →+* k', RingHom.ker φ = IsLocalRing.maximalIdeal ↥O ∧
      ∀ f : ↥O, W.evalAt (ι (f : F)) = φ f :=
  ⟨resHom ι O W hW hBO, ker_resHom ι O W hW hBO hloc, evalAt_eq_resHom ι O W hW hBO⟩

end package

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]

def placeOf {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) : Place K F where
  toValuationSubring := O
  algebraMap_mem' := hK
  ne_top' := hO
  isPrincipalIdealRing' := ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x O hK hO

theorem placeOf_toValuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (O : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ O) (hO : O ≠ ⊤) :
    (placeOf x O hK hO).toValuationSubring = O := rfl

theorem map_mem_valuationSubring_of_isIntegral {K K' F : Type*} [Field K] [Field K'] [Field F]
    [Algebra K K'] (g : K' →+* F)
    (B : ValuationSubring F) (hK : ∀ a : K, g (algebraMap K K' a) ∈ B) (c : K') (hc : IsIntegral K c) :
    g c ∈ B := by
  letI : Algebra K' F := g.toAlgebra
  letI : Algebra K F := (g.comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  letI : Algebra K ↥B := ((algebraMap K F).codRestrict B.toSubring hK).toAlgebra
  haveI : IsScalarTower K ↥B F := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have h1 : IsIntegral K (algebraMap K' F c) := hc.map (IsScalarTower.toAlgHom K K' F)
  have h2 : IsIntegral ↥B (algebraMap K' F c) := h1.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥B) (K := F)).mp h2
  show algebraMap K' F c ∈ B
  rw [← hy]; exact y.2

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem main (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [PerfectField κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : IntegralWeightOneForm κ M)
    (jbar : ↥(x1FunctionFieldC κ M)) (hjbar : (jbar : LaurentSeries κ) = jqModC κ)
    (O : ValuationSubring ↥(x1FunctionFieldC κ M))
    (hκO : ∀ c : κ, algebraMap κ ↥(x1FunctionFieldC κ M) c ∈ O) (hO : O ≠ ⊤)
    (hjO : jbar ∈ O)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ : ↥O →+* Ω),
      RingHom.ker φ = IsLocalRing.maximalIdeal ↥O → φ ⟨jbar, hjO⟩ ∈ ssJSet p Ω) :
    ∃ (b : ↥(x1FunctionFieldC κ M)) (ϖ : ↥O) (u : (↥O)ˣ) (m : ℤ),
      (b : LaurentSeries κ) = w.hasseRootFn ^ (p - 1) ∧ Irreducible ϖ ∧ IsCoprime m ((p - 1 : ℕ) : ℤ) ∧
      b = ((u : ↥O) : ↥(x1FunctionFieldC κ M)) * ((ϖ : ↥O) : ↥(x1FunctionFieldC κ M)) ^ m := by
  classical

  have hT := T_mem_Gamma1 M
  obtain ⟨hfin, -⟩ := finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index κ
    (CongruenceSubgroup.Gamma1 M) hT (CongruenceSubgroup.Gamma1 M) le_rfl (fun γ hγ => Or.inl hγ) jbar hjbar
  haveI : FiniteDimensional ↥(IntermediateField.adjoin κ ({jbar} : Set ↥(x1FunctionFieldC κ M)))
      ↥(x1FunctionFieldC κ M) := hfin
  let x : Place κ ↥(x1FunctionFieldC κ M) := placeOf jbar O hκO hO

  obtain ⟨hbmem, -, -⟩ := hasseRootFn_pow_mem_and_finite_and_isSeparable_igusaFunctionFieldX1C p M hM hpM κ w
  let b : ↥(x1FunctionFieldC κ M) := ⟨w.hasseRootFn ^ (p - 1), hbmem⟩
  have hb0 : b ≠ 0 := by
    intro h0
    have : (b : LaurentSeries κ) = 0 := by rw [h0]; rfl
    exact pow_ne_zero _ w.hasseRootFn_ne_zero this

  let κ' : Type := AlgebraicClosure κ
  haveI : CharP κ' p := charP_of_injective_algebraMap (algebraMap κ κ').injective p
  obtain ⟨ι, w', hιcoe, hιconst, hιj, hw', hgen⟩ := cf_package p κ κ' M w jbar hjbar

  obtain ⟨B, hBO, hBloc⟩ := exists_valuationSubring_comap_eq ι O
  have hκ'B : ∀ c : κ', algebraMap κ' ↥(x1FunctionFieldC κ' M) c ∈ B := by
    intro c
    refine map_mem_valuationSubring_of_isIntegral (K := κ) (algebraMap κ' ↥(x1FunctionFieldC κ' M)) B ?_ c
      (Algebra.IsIntegral.isIntegral (R := κ) c)
    intro a
    rw [← hιconst a, ← ValuationSubring.mem_comap, hBO]
    exact hκO a
  have hBtop : B ≠ ⊤ := by
    intro h; apply hO; rw [← hBO, h]; rfl
  obtain ⟨hfin', -⟩ := finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index κ'
    (CongruenceSubgroup.Gamma1 M) hT (CongruenceSubgroup.Gamma1 M) le_rfl (fun γ hγ => Or.inl hγ) (ι jbar) hιj
  haveI : FiniteDimensional ↥(IntermediateField.adjoin κ' ({ι jbar} : Set ↥(x1FunctionFieldC κ' M)))
      ↥(x1FunctionFieldC κ' M) := hfin'
  let W : Place κ' ↥(x1FunctionFieldC κ' M) := placeOf (ι jbar) B hκ'B hBtop
  have hWrat : W.IsRational := isRational_place_x1FunctionFieldC_of_isAlgClosed p M hM hpM κ' W

  have hord : ∀ f : ↥(x1FunctionFieldC κ M), W.ord (ι f) = x.ord f := by
    letI : Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) := ι.toAlgebra
    letI : Algebra κ ↥(x1FunctionFieldC κ' M) := ((algebraMap κ' ↥(x1FunctionFieldC κ' M)).comp (algebraMap κ κ')).toAlgebra
    haveI : IsScalarTower κ κ' ↥(x1FunctionFieldC κ' M) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    haveI : IsScalarTower κ ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ' M) := IsScalarTower.of_algebraMap_eq (fun a => (hιconst a).symm)
    exact Place.ord_algebraMap_eq_ord_of_comap_eq_of_isSeparable_of_adjoin_eq_top hgen x W hBO

  obtain ⟨φ, hker, hφ⟩ := exists_ringHom_ker_eq_and_evalAt_eq ι O W hWrat hBO hBloc
  have hssW : W.evalAt (ι jbar) ∈ ssJSet p κ' := by
    rw [show ι jbar = ι ((⟨jbar, hjO⟩ : ↥O) : ↥(x1FunctionFieldC κ M)) from rfl, hφ]
    exact hss κ' φ hker

  have hb' : ((ι b : ↥(x1FunctionFieldC κ' M)) : LaurentSeries κ') = w'.hasseRootFn ^ (p - 1) := by
    rw [hιcoe, hw']; simp [b, map_pow]
  have hjW : ι jbar ∈ W.toValuationSubring := by
    show ι jbar ∈ B
    rw [← ValuationSubring.mem_comap, hBO]; exact hjO
  have hgcd := gcd_sub_one_natAbs_ord_eq_one_of_evalAt_mem_ssJSet_of_coe_eq_hasseRootFn_pow p M hM hpM κ' w'
    (ι jbar) hιj (ι b) hb' W ⟨hjW, hssW⟩
  rw [hord] at hgcd

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible x.toValuationSubring
  obtain ⟨u, hu⟩ := x.exists_unit_mul_zpow hb0 hϖ
  refine ⟨b, ϖ, u, x.ord b, rfl, hϖ, ?_, hu⟩
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  simpa [Int.gcd] using hgcd

end B3E100
p2m_reactivate "P2MW.S_ModularCurve_exists_irreducible_isCoprime_eq_mul_pow_of_coe_eq_hasseRootFn_pow_of_mem_ssJSet.B3E100"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_irreducible_isCoprime_eq_mul_pow_of_coe_eq_hasseRootFn_pow_of_mem_ssJSet.B3E100"

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [PerfectField κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (jbar : ↥(ModularCurve.x1FunctionFieldC κ M)) (hjbar : (jbar : LaurentSeries κ) = ModularCurve.jqModC κ)
    (O : ValuationSubring ↥(ModularCurve.x1FunctionFieldC κ M))
    (hκO : ∀ c : κ, algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) c ∈ O) (hO : O ≠ ⊤)
    (hjO : jbar ∈ O)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ : ↥O →+* Ω),
      RingHom.ker φ = IsLocalRing.maximalIdeal ↥O → φ ⟨jbar, hjO⟩ ∈ ModularCurve.ssJSet p Ω) :
    ∃ (b : ↥(ModularCurve.x1FunctionFieldC κ M)) (ϖ : ↥O) (u : (↥O)ˣ) (m : ℤ),
      (b : LaurentSeries κ) = w.hasseRootFn ^ (p - 1) ∧ Irreducible ϖ ∧ IsCoprime m ((p - 1 : ℕ) : ℤ) ∧
      b = ((u : ↥O) : ↥(ModularCurve.x1FunctionFieldC κ M)) * ((ϖ : ↥O) : ↥(ModularCurve.x1FunctionFieldC κ M)) ^ m :=
  B3E100.main p κ M hM hpM w jbar hjbar O hκO hO hjO hss

end S_ModularCurve_exists_irreducible_isCoprime_eq_mul_pow_of_coe_eq_hasseRootFn_pow_of_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_exists_irreducible_isCoprime_eq_mul_pow_of_coe_eq_hasseRootFn_pow_of_mem_ssJSet (solution)
