-- Prove2me | solution 1 for ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/df697cee-47c5-5ae4-aca7-604b6a96639c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import Theorems.Thm_ModularCurve_exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
import Theorems.Thm_ModularForm_exists_qCoeff_slash_eq_mul_of_forall_qCoeff_eq_mul_of_prime_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
import Theorems.Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC x1FunctionFieldC x1FunctionFieldBar coeffMap coeffMap_coeff coeffEmb coeffEmb_coeff laurentBaseChange xHFunctionFieldC xHFunctionFieldC_bot xHFunctionFieldBar jqModC thetaL thetaL_apply qExpansionDiffAlong exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd genusFF_qExpFunctionFieldC_eq_of_ringHom exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm laurentBaseChange_adjoin qExpansionDiffAlong_D qExpansionDiffAlong_smul theta_coeff coeff_jqModC_neg_one"
p2m_open "ModularCurve~coeffEmb_injective~coeffMap_ofPowerSeries~IsCusp"

namespace X1OmegaIso

open scoped BigOperators TensorProduct ModularForm MatrixGroups
p2m_open "ModularCurve~coeffEmb_injective~coeffMap_ofPowerSeries~IsCusp P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve AlgebraicCurve ModularForm ModularFormClass Complex IntermediateField CongruenceSubgroup"

p2m_open "UpperHalfPlane~I"

section LinDisjoint

variable {K₀ K : Type*} [Field K₀] [Field K] [Algebra K₀ K] {ι S : Type*} [Fintype ι]

theorem forall_eq_zero_of_forall_baseField_eq_zero (v : ι → S → K₀)
    (hv : ∀ d : ι → K₀, (∀ s, ∑ i, d i * v i s = 0) → ∀ i, d i = 0)
    (g : ι → K) (hg : ∀ s, ∑ i, g i * algebraMap K₀ K (v i s) = 0) : ∀ i, g i = 0 := by
  classical
  let B := Module.Basis.ofVectorSpace K₀ K
  have key : ∀ l, ∀ i, B.repr (g i) l = 0 := by
    intro l
    refine hv (fun i => B.repr (g i) l) ?_
    intro s
    have h1 : B.repr (∑ i, g i * algebraMap K₀ K (v i s)) l = 0 := by
      rw [hg s, map_zero, Finsupp.zero_apply]
    rw [map_sum, Finsupp.finsetSum_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (g i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  intro i
  rw [← B.repr.map_eq_zero_iff]
  ext l
  exact key l i

end LinDisjoint

section IntRel

variable (K : Type*) [Field K] {ι S : Type*} [Fintype ι]

theorem forall_eq_zero_of_forall_intRel (v : ι → S → ℤ)
    (H : ∀ m : ι → ℤ, (∀ s, ((∑ i, m i * v i s : ℤ) : K) = 0) → ∀ i, (m i : K) = 0)
    (g : ι → K) (hg : ∀ s, ∑ i, g i * (v i s : K) = 0) : ∀ i, g i = 0 := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · haveI := Fact.mk hprime
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    refine forall_eq_zero_of_forall_baseField_eq_zero (K₀ := ZMod p)
      (fun i s => (v i s : ZMod p)) ?_ g ?_
    · intro d hd i
      have hm : ∀ s, ((∑ i, ((d i).cast : ℤ) * v i s : ℤ) : K) = 0 := by
        intro s
        have h2 : ((∑ i, ((d i).cast : ℤ) * v i s : ℤ) : ZMod p) = 0 := by
          rw [← hd s, Int.cast_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Int.cast_mul, ZMod.intCast_zmod_cast]
        have h3 := congrArg (algebraMap (ZMod p) K) h2
        rwa [map_intCast, map_zero] at h3
      have h4 : algebraMap (ZMod p) K (d i) = 0 := by
        rw [← ZMod.intCast_zmod_cast (d i), map_intCast]
        exact H _ hm i
      exact (map_eq_zero_iff _ (algebraMap (ZMod p) K).injective).mp h4
    · intro s
      simp_rw [map_intCast]
      exact hg s
  · haveI : CharZero K := CharP.charP_to_charZero K
    refine forall_eq_zero_of_forall_baseField_eq_zero (K₀ := ℚ)
      (fun i s => (v i s : ℚ)) ?_ g ?_
    · intro d hd i
      set D : ℕ := ∏ i, (d i).den with hD
      have hD0 : (D : ℚ) ≠ 0 := by
        rw [hD]
        exact_mod_cast Finset.prod_ne_zero_iff.mpr fun i _ => (d i).den_nz
      have hint : ∀ i, ∃ m : ℤ, (D : ℚ) * d i = m := by
        intro i
        obtain ⟨c, hc⟩ : (d i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        refine ⟨c * (d i).num, ?_⟩
        rw [hc]
        push_cast
        rw [mul_comm ((d i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
      choose m hm using hint
      have hmK : ∀ s, ((∑ i, m i * v i s : ℤ) : K) = 0 := by
        intro s
        have h1 : (∑ i, m i * v i s : ℤ) = 0 := by
          have h : ((∑ i, m i * v i s : ℤ) : ℚ) = D * ∑ i, d i * v i s := by
            push_cast
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← hm i]
            ring
          rw [hd s, mul_zero] at h
          exact_mod_cast h
        rw [h1, Int.cast_zero]
      have h5 : (m i : K) = 0 := H m hmK i
      have hmi : m i = 0 := by exact_mod_cast h5
      have h6 : (D : ℚ) * d i = 0 := by rw [hm i, hmi, Int.cast_zero]
      exact (mul_eq_zero.mp h6).resolve_left hD0
    · intro s
      simp_rw [map_intCast]
      exact hg s

end IntRel

section Lattice

variable (M : ℕ)

abbrev S2 : Type := CuspForm (Gamma1 M) 2

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma hasSum_qCoeff (f : S2 M) (τ : UpperHalfPlane) :
    HasSum (fun m ↦ qCoeff f m * Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
  have := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods M))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  (first | exact this | simpa only [smul_eq_mul] using this | (have h__ := this; simp only [smul_eq_mul] at h__; exact h__))

lemma eq_zero_of_forall_qCoeff_eq_zero (f : S2 M) (h : ∀ n, qCoeff f n = 0) : f = 0 := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hs := hasSum_qCoeff M f τ
  have hz : (fun m ↦ qCoeff f m * Function.Periodic.qParam 1 τ ^ m) = fun _ => 0 := by
    funext m
    rw [h m, zero_mul]
  rw [hz] at hs
  simpa using hs.unique hasSum_zero

def qCoeffLin (n : ℕ) : S2 M →ₗ[ℂ] ℂ where
  toFun f := qCoeff f n
  map_add' f g := by
    simp only [qCoeff, CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) f g, map_add]
  map_smul' c f := by
    simp only [qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M) c f]
    simp

@[scoped simp] lemma qCoeffLin_apply (n : ℕ) (f : S2 M) : qCoeffLin M n f = qCoeff f n := rfl

theorem sl_slash (f : UpperHalfPlane → ℂ) (k : ℤ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl

def dsSet : Set (S2 M) :=
  {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
      ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈ Set.range ((↑) : ℤ → ℂ)}

abbrev Lat : Submodule ℤ (S2 M) :=
  Submodule.span ℤ
    {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
        ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈ Set.range ((↑) : ℤ → ℂ)}

lemma Lat_eq : Lat M = Submodule.span ℤ (dsSet M) := rfl

variable {M}

def qCoeffSlashLin {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (n : ℕ) : S2 M →ₗ[ℂ] ℂ :=
  qCoeffLin M n ∘ₗ CuspForm.slashLinOfMemGamma0 M 2 hγ

lemma qCoeffSlashLin_apply {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (n : ℕ) (f : S2 M) :
    qCoeffSlashLin hγ n f = qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n := rfl

theorem exists_int_qCoeff_slash_of_mem {f : S2 M} (hf : f ∈ Lat M) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) (n : ℕ) :
    ∃ m : ℤ, qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n = (m : ℂ) := by
  rw [Lat_eq] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, hm⟩ := hx γ hγ n
      exact ⟨m, hm.symm⟩
  | zero => exact ⟨0, by rw [← qCoeffSlashLin_apply hγ, map_zero, Int.cast_zero]⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [← qCoeffSlashLin_apply hγ, map_add, qCoeffSlashLin_apply, qCoeffSlashLin_apply, ha, hb,
        Int.cast_add]
  | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      refine ⟨a * b, ?_⟩
      rw [← qCoeffSlashLin_apply hγ, map_zsmul, qCoeffSlashLin_apply, hb, zsmul_eq_mul, Int.cast_mul]

theorem exists_int_qCoeff_of_mem {f : S2 M} (hf : f ∈ Lat M) (n : ℕ) :
    ∃ m : ℤ, qCoeff f n = (m : ℂ) := by
  obtain ⟨m, hm⟩ := exists_int_qCoeff_slash_of_mem hf (Subgroup.one_mem (Gamma0 M)) n
  refine ⟨m, ?_⟩
  rw [← hm, sl_slash, map_one, SlashAction.slash_one]

def coefZ (f : ↥(Lat M)) (n : ℕ) : ℤ := (exists_int_qCoeff_of_mem f.2 n).choose

theorem coefZ_spec (f : ↥(Lat M)) (n : ℕ) : qCoeff (f : S2 M) n = (coefZ f n : ℂ) :=
  (exists_int_qCoeff_of_mem f.2 n).choose_spec

theorem coefZ_eq_of_forall (f : ↥(Lat M)) (a : ℕ → ℤ) (ha : ∀ n, qCoeff (f : S2 M) n = (a n : ℂ)) :
    coefZ f = a := by
  funext n
  have h := (coefZ_spec f n).symm.trans (ha n)
  exact_mod_cast h

def coefZHom (n : ℕ) : ↥(Lat M) →ₗ[ℤ] ℤ where
  toFun f := coefZ f n
  map_add' f g := by
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_add, ← coefZ_spec, ← coefZ_spec, ← coefZ_spec, Submodule.coe_add, ← qCoeffLin_apply,
      map_add, qCoeffLin_apply, qCoeffLin_apply]
  map_smul' a f := by
    apply Int.cast_injective (α := ℂ)
    rw [smul_eq_mul, Int.cast_mul, ← coefZ_spec, ← coefZ_spec, Submodule.coe_smul, ← qCoeffLin_apply,
      LinearMap.map_smul_of_tower, qCoeffLin_apply, zsmul_eq_mul, RingHom.id_apply]

@[scoped simp] lemma coefZHom_apply (n : ℕ) (f : ↥(Lat M)) : coefZHom n f = coefZ f n := rfl

theorem coefZ_add (f g : ↥(Lat M)) : coefZ (f + g) = coefZ f + coefZ g := by
  funext n
  exact (coefZHom (M := M) n).map_add f g

variable (M) [NeZero M]

theorem finiteDimensional_S2 : FiniteDimensional ℂ (S2 M) := by
  obtain ⟨n, b, -⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast M 2
  exact Module.Finite.of_basis b

theorem exists_finset_qCoeff_eq_zero_imp :
    ∃ s : Finset ℕ, ∀ f : S2 M, (∀ n ∈ s, qCoeff f n = 0) → f = 0 := by
  classical
  haveI := finiteDimensional_S2 M
  let Kf : Finset ℕ → Submodule ℂ (S2 M) := fun s => ⨅ n ∈ s, LinearMap.ker (qCoeffLin M n)
  have hanti : ∀ s t : Finset ℕ, s ⊆ t → Kf t ≤ Kf s := by
    intro s t hst
    exact biInf_mono hst
  obtain ⟨W, ⟨s₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ (S2 M))).has_min (Set.range Kf) ⟨Kf ∅, ∅, rfl⟩
  refine ⟨s₀, fun f hf => ?_⟩
  have hfK : f ∈ Kf s₀ := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffLin_apply]
    exact hf
  apply eq_zero_of_forall_qCoeff_eq_zero M f
  intro n
  have hle : Kf (insert n s₀) ≤ Kf s₀ := hanti _ _ (Finset.subset_insert n s₀)
  have hnlt : ¬ Kf (insert n s₀) < Kf s₀ := hmin _ ⟨insert n s₀, rfl⟩
  have heq : Kf (insert n s₀) = Kf s₀ := (eq_or_lt_of_le hle).resolve_right hnlt
  have hf' : f ∈ Kf (insert n s₀) := heq ▸ hfK
  simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, qCoeffLin_apply] at hf'
  exact hf' n (Finset.mem_insert_self n s₀)

theorem moduleFinite_Lat : Module.Finite ℤ ↥(Lat M) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_qCoeff_eq_zero_imp M
  let ev : ↥(Lat M) →ₗ[ℤ] (↥s → ℤ) := LinearMap.pi fun n => coefZHom (M := M) n.1
  refine Module.Finite.of_injective ev ?_
  intro f g hfg
  rw [← sub_eq_zero]
  apply Subtype.ext
  rw [Submodule.coe_sub, Submodule.coe_zero]
  have h : ev (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  apply hs
  intro n hn
  have hn' := congrFun h ⟨n, hn⟩
  simp only [ev, LinearMap.pi_apply, coefZHom_apply, Pi.zero_apply] at hn'
  rw [← Submodule.coe_sub, coefZ_spec, hn', Int.cast_zero]

scoped instance isTorsionFree_Lat : Module.IsTorsionFree ℤ ↥(Lat M) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  have h' : (r : ℂ) • ((m : ↥(Lat M)) : S2 M) = 0 := by
    rw [Int.cast_smul_eq_zsmul, ← Submodule.coe_smul_of_tower, h, Submodule.coe_zero]
  rcases smul_eq_zero.mp h' with hr | hm
  · exact Or.inl (by exact_mod_cast hr)
  · exact Or.inr (Subtype.ext hm)

theorem moduleFree_Lat : Module.Free ℤ ↥(Lat M) := by
  haveI := moduleFinite_Lat M
  exact Module.free_of_finite_type_torsion_free'

variable {M}

theorem exists_eq_smul_of_forall_dvd {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (f : ↥(Lat M))
    (hdvd : ∀ n, (p : ℤ) ∣ coefZ f n) : ∃ g : ↥(Lat M), f = (p : ℤ) • g := by
  haveI := Fact.mk hp
  choose B hB using hdvd
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  let g : S2 M := ((p : ℂ)⁻¹) • (f : S2 M)

  have hint : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
      qCoeff ((⇑(ModularFormClass.modularForm (f : S2 M)) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈
        Set.range ((↑) : ℤ → ℂ) := by
    intro γ hγ n
    obtain ⟨m, hm⟩ := exists_int_qCoeff_slash_of_mem f.2 hγ n
    exact ⟨m, hm.symm⟩
  have hpf : ∀ n : ℕ, ∃ m : ℤ,
      qCoeff ((⇑(ModularFormClass.modularForm (f : S2 M)) : UpperHalfPlane → ℂ)) n = (p : ℂ) * m := by
    intro n
    refine ⟨B n, ?_⟩
    change qCoeff (f : S2 M) n = _
    rw [coefZ_spec, hB n]
    push_cast
    ring
  have hg : g ∈ Lat M := by
    refine Submodule.subset_span ?_
    intro γ hγ n
    obtain ⟨m, hm⟩ :=
      ModularForm.exists_qCoeff_slash_eq_mul_of_forall_qCoeff_eq_mul_of_prime_not_dvd M p hpM 2
        (ModularFormClass.modularForm (f : S2 M)) hint hpf γ hγ n
    refine ⟨m, ?_⟩
    change (m : ℂ) = qCoeffSlashLin hγ n g
    rw [map_smul, qCoeffSlashLin_apply, smul_eq_mul]
    change (m : ℂ) = (p : ℂ)⁻¹ * qCoeff ((⇑(ModularFormClass.modularForm (f : S2 M)) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n
    rw [hm, ← mul_assoc, inv_mul_cancel₀ hpC, one_mul]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  rw [Submodule.coe_smul_of_tower]
  change (f : S2 M) = (p : ℤ) • (((p : ℂ)⁻¹) • (f : S2 M))
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, Int.cast_natCast, mul_inv_cancel₀ hpC, one_smul]

theorem intRel_trivial (K : Type*) [Field K] (hM : (M : K) ≠ 0) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ ↥(Lat M)) (m : ι → ℤ)
    (h : ∀ n : ℕ, ((∑ i, m i * coefZ (b i) n : ℤ) : K) = 0) : ∀ i, (m i : K) = 0 := by
  classical
  set f : ↥(Lat M) := ∑ i, m i • b i with hfdef
  have hf : ∀ n, coefZ f n = ∑ i, m i * coefZ (b i) n := by
    intro n
    rw [← coefZHom_apply, hfdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, coefZHom_apply, smul_eq_mul]
  have hrepr : ∀ i, b.repr f i = m i := fun i => by
    rw [hfdef, b.repr_sum_self]
  obtain ⟨p, hp⟩ := CharP.exists K
  have hdvd : ∀ n, (p : ℤ) ∣ coefZ f n := fun n =>
    (CharP.intCast_eq_zero_iff K p _).mp (by rw [hf]; exact h n)
  intro i
  rcases CharP.char_is_prime_or_zero K p with hprime | hp0
  · have hpM : ¬ p ∣ M := by
      rintro ⟨c, rfl⟩
      apply hM
      rw [Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul]
    obtain ⟨g, hfg⟩ := exists_eq_smul_of_forall_dvd hprime hpM f hdvd
    have h2 : b.repr f i = (p : ℤ) * b.repr g i := by
      rw [hfg, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
    rw [← hrepr i, h2, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
  · subst hp0
    have hf0 : f = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_zero]
      refine eq_zero_of_forall_qCoeff_eq_zero M _ fun n => ?_
      rw [coefZ_spec, show coefZ f n = 0 from by simpa using hdvd n, Int.cast_zero]
    rw [← hrepr i, hf0, map_zero, Finsupp.zero_apply, Int.cast_zero]

variable (M)

theorem linearIndependent_coe_basis {ι : Type*} [Fintype ι] (c : Module.Basis ι ℤ ↥(Lat M)) :
    LinearIndependent ℂ (fun i => ((c i : ↥(Lat M)) : S2 M)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine forall_eq_zero_of_forall_intRel ℂ (fun i n => coefZ (c i) n)
    (intRel_trivial ℂ (NeZero.ne (M : ℂ)) c) g ?_
  intro n
  have h := congrArg (qCoeffLin M n) hg
  rw [map_sum, map_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, qCoeffLin_apply, coefZ_spec, smul_eq_mul]

theorem card_basis_eq_finrank {ι : Type*} [Fintype ι]
    (c : Module.Basis ι ℤ ↥(Lat M)) : Fintype.card ι = Module.finrank ℂ (S2 M) := by
  classical
  haveI := finiteDimensional_S2 M
  haveI := moduleFinite_Lat M
  refine le_antisymm (linearIndependent_coe_basis M c).fintype_card_le_finrank ?_
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast M 2
  have hmem : ∀ i, b i ∈ Lat M := fun i => Submodule.subset_span (hb i)
  let b' : Fin n → ↥(Lat M) := fun i => ⟨b i, hmem i⟩
  have hbZ : LinearIndependent ℤ (fun i => (b i : S2 M)) := by
    refine b.linearIndependent.restrict_scalars ?_
    intro r s hrs
    have h : (r : ℂ) = (s : ℂ) := by simpa [zsmul_eq_mul] using hrs
    exact_mod_cast h
  have hb' : LinearIndependent ℤ b' := LinearIndependent.of_comp (Lat M).subtype hbZ
  have h1 : Fintype.card (Fin n) ≤ Module.finrank ℤ ↥(Lat M) := hb'.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c] at *
  exact h1

end Lattice

section Package

universe u v

variable (k : Type u) [Field k] [IsAlgClosed k] (F : Type v) [Field F] [Algebra k F]
  [Algebra.EssFiniteType k F] [IsCurveOver k F]

theorem genus_eq_genusFF_of_isAlgClosed :
    haveI : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_of_isCurveOver
    genus k F = genusFF k F := by
  classical
  haveI : PerfectField k := IsAlgClosed.perfectField k
  haveI hcd : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place k F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨t, ht, hfin, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  haveI := hfin
  haveI := hsep
  haveI : IsCurveOver k (RatFunc k) := isCurveOver_ratFunc k
  haveI : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  haveI : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  haveI : ∀ v : Place k (RatFunc k), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let e : RatFunc k ≃ₐ[k] k⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc k) F := ((algebraMap k⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc k) F) (e.symm.toRingEquiv : k⟮t⟯ →+* RatFunc k)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap k⟮t⟯ F) := by
    ext y
    show algebraMap k⟮t⟯ F (e (e.symm y)) = algebraMap k⟮t⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap k F a = algebraMap k⟮t⟯ F (e (algebraMap k (RatFunc k) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc k) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc k) F := Algebra.IsIntegral.of_finite _ _
  have hRR : FunctionFieldRiemannRoch k F :=
    functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := k) (F := F)
  have hC : ConstantsAreBase k F := constantsAreBase_of_isAlgClosed k F
  have hSG : StichtenothGenusExists k F := stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic k F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  exact genus_eq_genusFF hRR hWDA hC

theorem finrank_regularDifferentials_eq_genusFF :
    Module.Finite k ↥(regularDifferentials k F) ∧
      Module.finrank k ↥(regularDifferentials k F) = genusFF k F := by
  haveI : PerfectField k := IsAlgClosed.perfectField k
  haveI hcd : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_of_isCurveOver
  obtain ⟨hfin, hrank⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := k) (F := F)
  exact ⟨hfin, hrank.trans (genus_eq_genusFF_of_isAlgClosed k F)⟩

end Package

section Fields

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem curve_structure (K : Type*) [Field K] [IsAlgClosed K] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    (∃ x : qExpFunctionFieldC K Γ, (x : LaurentSeries K) = jqModC K ∧ Transcendental K x ∧
        FiniteDimensional (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
          (qExpFunctionFieldC K Γ)) ∧
      IsCurveOver K ↥(qExpFunctionFieldC K Γ) ∧ Algebra.EssFiniteType K ↥(qExpFunctionFieldC K Γ) := by
  haveI : PerfectField K := IsAlgClosed.perfectField K
  obtain ⟨x, hxj, htr, hfd⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K Γ hT
  exact ⟨⟨x, hxj, htr, hfd⟩, isCurveOver_of_transcendental_of_perfectField htr hfd,
    essFiniteType_of_transcendental_of_finiteDimensional htr hfd⟩

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ))

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext i
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hi
  · exact map_zero φ
  · rw [PowerSeries.coeff_map]

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  rw [coeffEmb, intSeriesC, coeffMap_ofPowerSeries, intSeriesC]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffEmb_injective : Function.Injective (coeffEmb L) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ L).injective h1

theorem image_intFormRatiosC : coeffEmb L '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  ext z
  constructor
  · rintro ⟨_, ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    have hgL : intSeriesC L pg ≠ 0 := by
      rw [← coeffEmb_intSeriesC L]
      exact (map_ne_zero_iff _ (coeffEmb_injective L)).mpr hg0
    refine ⟨κ, f, g, pf, pg, hf, hg, hgL, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hgQ : intSeriesC ℚ pg ≠ 0 := by
      intro h
      apply hg0
      rw [← coeffEmb_intSeriesC L, h, map_zero]
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨κ, f, g, pf, pg, hf, hg, hgQ, rfl⟩, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

theorem laurentBaseChange_qExpFunctionFieldC :
    laurentBaseChange L (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC L Γ := by
  rw [qExpFunctionFieldC, laurentBaseChange_adjoin, image_intFormRatiosC]
  rfl

end BaseChange

theorem x1FunctionFieldC_eq (K : Type*) [Field K] (M : ℕ) :
    x1FunctionFieldC K M = qExpFunctionFieldC K (Gamma1 M) := rfl

theorem x1FunctionFieldBar_eq (M : ℕ) :
    x1FunctionFieldBar M = qExpFunctionFieldC (AlgebraicClosure ℚ) (Gamma1 M) :=
  laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (Gamma1 M)

theorem genusFF_x1FunctionFieldC_eq (k : Type*) [Field k] [IsAlgClosed k] (M : ℕ) [NeZero M]
    (hM : (M : k) ≠ 0) :
    genusFF k ↥(x1FunctionFieldC k M) = genusFF (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hprime | hp0
  · haveI := Fact.mk hprime
    have hpM : ¬ p ∣ M := by
      rintro ⟨c, rfl⟩
      apply hM
      rw [Nat.cast_mul, CharP.cast_eq_zero k p, zero_mul]
    have h := ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd M ⊥ hpM k
    rw [xHFunctionFieldC_bot] at h
    rw [h]

    change genusFF (AlgebraicClosure ℚ)
        ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionFieldC ℚ M ⊥)) = _
    rw [xHFunctionFieldC_bot]
  · subst hp0
    haveI : CharZero k := CharP.charP_to_charZero k
    letI : Algebra ℚ k := DivisionRing.toRatAlgebra
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    let φ : AlgebraicClosure ℚ →+* k :=
      ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] k) : AlgebraicClosure ℚ →+* k)
    obtain ⟨⟨x, -, htr, hfd⟩, -, -⟩ := curve_structure (AlgebraicClosure ℚ) (Gamma1 M) (T_mem_Gamma1 M)
    have h := ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom φ (Gamma1 M) ⟨x, htr, hfd⟩
    rw [x1FunctionFieldC_eq, h, x1FunctionFieldBar_eq]

theorem finrank_S2_eq_genusFF (M : ℕ) [NeZero M] :
    Module.finrank ℂ (S2 M) = genusFF (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι₀ : AlgebraicClosure ℚ →+* ℂ :=
    ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)
  letI := ι₀.toAlgebra
  obtain ⟨e, -⟩ := ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm M ι₀

  obtain ⟨-, hco, hess⟩ := curve_structure (AlgebraicClosure ℚ) (Gamma1 M) (T_mem_Gamma1 M)
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) := by
    rw [x1FunctionFieldBar_eq]; exact hco
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) := by
    rw [x1FunctionFieldBar_eq]; exact hess
  obtain ⟨hfin, hrank⟩ :=
    finrank_regularDifferentials_eq_genusFF (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M)
  haveI := hfin
  rw [← hrank, ← e.finrank_eq, Module.finrank_baseChange]

end Fields

section DiffSide

universe u

variable (k : Type u) [Field k] (M : ℕ) [NeZero M]

def red (a : ℕ → ℤ) : LaurentSeries k :=
  HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k))

theorem red_coeff (a : ℕ → ℤ) (n : ℕ) : (red k a).coeff (n : ℤ) = (a n : k) := by
  rw [red, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk]

theorem red_add (a b : ℕ → ℤ) : red k (a + b) = red k a + red k b := by
  rw [red, red, red, ← map_add]
  congr 1
  ext n
  simp [PowerSeries.coeff_mk]

theorem thetaL_jqModC_ne_zero : thetaL k (jqModC k) ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries k => x.coeff (-1 : ℤ)) h
  beta_reduce at h1
  rw [thetaL_apply, theta_coeff, coeff_jqModC_neg_one] at h1
  simp at h1

variable [IsAlgClosed k]

abbrev F1 : IntermediateField k (LaurentSeries k) := x1FunctionFieldC k M

scoped instance isCurveOver_F1 : IsCurveOver k ↥(F1 k M) :=
  (curve_structure k (Gamma1 M) (T_mem_Gamma1 M)).2.1

scoped instance essFiniteType_F1 : Algebra.EssFiniteType k ↥(F1 k M) :=
  (curve_structure k (Gamma1 M) (T_mem_Gamma1 M)).2.2

theorem qExpansionDiffAlong_val_injective :
    Function.Injective (qExpansionDiffAlong (F1 k M).val) := by
  obtain ⟨⟨j, hj, -, -⟩, -, -⟩ := curve_structure k (Gamma1 M) (T_mem_Gamma1 M)
  change ↥(F1 k M) at j
  set σ := (F1 k M).val with hσ
  set Dj : Ω[↥(F1 k M)⁄k] := KaehlerDifferential.D k ↥(F1 k M) j with hDjdef
  have hσj : σ j = jqModC k := hj
  have hθ : thetaL k (σ j) ≠ 0 := by rw [hσj]; exact thetaL_jqModC_ne_zero k
  have h2 : qExpansionDiffAlong σ Dj = thetaL k (σ j) := qExpansionDiffAlong_D σ j
  have hDj : Dj ≠ 0 := by
    intro h
    rw [h] at h2
    exact hθ (h2.symm.trans (LinearMap.map_zero _))
  have hspan := (finrank_eq_one_iff_of_nonzero' Dj hDj).mp IsCurveOver.finrank_kaehler
  intro ω₁ ω₂ hω
  rw [← sub_eq_zero] at hω ⊢
  rw [← LinearMap.map_sub] at hω
  obtain ⟨c, hc⟩ := hspan (ω₁ - ω₂)
  have hsm : qExpansionDiffAlong σ (c • Dj) = σ c * qExpansionDiffAlong σ Dj :=
    qExpansionDiffAlong_smul σ c Dj
  have key : σ c * thetaL k (σ j) = 0 := by
    rw [← h2, ← hsm, hc]
    exact hω
  rw [← hc]
  rcases mul_eq_zero.mp key with hc0 | hθ0
  · have : c = 0 := by
      have h' : ((c : LaurentSeries k)) = 0 := hc0
      exact_mod_cast h'
    rw [this]
    exact zero_smul _ _
  · exact absurd hθ0 hθ

variable (hM : (M : k) ≠ 0)

abbrev Reg := ↥(regularDifferentials k ↥(F1 k M))

include hM in

theorem exists_reg (f : ↥(Lat M)) : ∃ ω : Reg k M,
    qExpansionDiffAlong (F1 k M).val (ω : Ω[↥(F1 k M)⁄k]) = red k (coefZ f) := by
  obtain ⟨ω, hω, hq⟩ :=
    ModularCurve.exists_mem_regularDifferentials_qExpFunctionFieldC_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
      k M hM (Gamma1 M) le_rfl (Gamma1_in_Gamma0 M) (f : S2 M) (coefZ f) (coefZ_spec f)
  exact ⟨⟨ω, hω⟩, hq⟩

def regOf (f : ↥(Lat M)) : Reg k M := (exists_reg k M hM f).choose

theorem regOf_spec (f : ↥(Lat M)) :
    qExpansionDiffAlong (F1 k M).val (regOf k M hM f : Ω[↥(F1 k M)⁄k]) = red k (coefZ f) :=
  (exists_reg k M hM f).choose_spec

theorem regOf_add (f g : ↥(Lat M)) : regOf k M hM (f + g) = regOf k M hM f + regOf k M hM g := by
  apply Subtype.ext
  apply qExpansionDiffAlong_val_injective k M
  have h4 := (qExpansionDiffAlong (F1 k M).val).map_add
    (regOf k M hM f : Ω[↥(F1 k M)⁄k]) (regOf k M hM g : Ω[↥(F1 k M)⁄k])
  rw [regOf_spec, coefZ_add, red_add, ← regOf_spec k M hM f, ← regOf_spec k M hM g, ← h4]
  rfl

def regHom : ↥(Lat M) →ₗ[ℤ] Reg k M :=
  (AddMonoidHom.mk' (regOf k M hM) (regOf_add k M hM)).toIntLinearMap

@[scoped simp] theorem regHom_apply (f : ↥(Lat M)) : regHom k M hM f = regOf k M hM f := rfl

def e0 : k ⊗[ℤ] ↥(Lat M) →ₗ[k] Reg k M := (regHom k M hM).liftBaseChange k

theorem e0_tmul (c : k) (f : ↥(Lat M)) : e0 k M hM (c ⊗ₜ[ℤ] f) = c • regOf k M hM f := by
  rw [e0, LinearMap.liftBaseChange_tmul, regHom_apply]

theorem qexp_e0_tmul (c : k) (f : ↥(Lat M)) :
    qExpansionDiffAlong (F1 k M).val (e0 k M hM (c ⊗ₜ[ℤ] f) : Ω[↥(F1 k M)⁄k]) =
      c • red k (coefZ f) := by
  rw [e0_tmul, ← regOf_spec, ← LinearMap.map_smul]
  rfl

def qe0 : k ⊗[ℤ] ↥(Lat M) →ₗ[k] LaurentSeries k :=
  (qExpansionDiffAlong (F1 k M).val) ∘ₗ ((regularDifferentials k ↥(F1 k M)).subtype ∘ₗ e0 k M hM)

theorem qe0_apply (x : k ⊗[ℤ] ↥(Lat M)) :
    qe0 k M hM x = qExpansionDiffAlong (F1 k M).val (e0 k M hM x : Ω[↥(F1 k M)⁄k]) :=
  rfl

include hM in

theorem e0_injective : Function.Injective (e0 k M hM) := by
  classical
  haveI := moduleFree_Lat M
  haveI := moduleFinite_Lat M
  let b := Module.Free.chooseBasis ℤ ↥(Lat M)
  let bk : Module.Basis _ k (k ⊗[ℤ] ↥(Lat M)) := Algebra.TensorProduct.basis k b
  rw [injective_iff_map_eq_zero]
  intro x hx
  set c : Module.Free.ChooseBasisIndex ℤ ↥(Lat M) → k := fun i => bk.repr x i with hcdef
  have hxsum : x = ∑ i, c i • ((1 : k) ⊗ₜ[ℤ] b i) := by
    conv_lhs => rw [← bk.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
  have hq : ∀ n : ℕ, ∑ i, c i * (coefZ (b i) n : k) = 0 := by
    intro n
    have h0 : qe0 k M hM x = 0 := by
      rw [qe0_apply, hx]
      exact LinearMap.map_zero _
    rw [hxsum, map_sum] at h0
    have h1 : (∑ i, qe0 k M hM (c i • ((1 : k) ⊗ₜ[ℤ] b i))).coeff (n : ℤ) = 0 := by
      rw [h0]; rfl
    rw [HahnSeries.coeff_sum] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, qe0_apply, qexp_e0_tmul, one_smul, HahnSeries.coeff_smul, red_coeff, smul_eq_mul]
  have hc : ∀ i, c i = 0 :=
    forall_eq_zero_of_forall_intRel k (fun i n => coefZ (b i) n) (intRel_trivial k hM b) c hq
  rw [hxsum]
  exact Finset.sum_eq_zero fun i _ => by rw [hc i, zero_smul]

end DiffSide

section Main

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] (M : ℕ) [NeZero M] (hM : (M : k) ≠ 0)

include hM in
theorem main :
    (∃ e : k ⊗[ℤ] ↥(Lat M) ≃ₗ[k] Reg k M,
      ∀ (c : k) (f : ↥(Lat M)) (a : ℕ → ℤ),
        (∀ n : ℕ, ModularFormClass.qCoeff ((f : S2 M) : UpperHalfPlane → ℂ) n = (a n : ℂ)) →
        qExpansionDiffAlong (x1FunctionFieldC k M).val
            (e (c ⊗ₜ[ℤ] f) : Ω[↥(x1FunctionFieldC k M)⁄k]) =
          c • HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k))) ∧
    Function.Injective
      (fun ω : Reg k M => qExpansionDiffAlong (x1FunctionFieldC k M).val (ω : Ω[↥(x1FunctionFieldC k M)⁄k])) := by
  classical
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨hfinΩ, hrankΩ⟩ := finrank_regularDifferentials_eq_genusFF k ↥(F1 k M)
    haveI : Module.Finite k (Reg k M) := hfinΩ

    haveI := moduleFree_Lat M
    haveI := moduleFinite_Lat M
    let b := Module.Free.chooseBasis ℤ ↥(Lat M)
    have h1 : Module.finrank k (k ⊗[ℤ] ↥(Lat M)) =
        Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥(Lat M)) :=
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis k b)
    have h2 : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥(Lat M)) = Module.finrank ℂ (S2 M) :=
      card_basis_eq_finrank M b
    have hdim : Module.finrank k (k ⊗[ℤ] ↥(Lat M)) = Module.finrank k (Reg k M) := by
      rw [h1, h2, finrank_S2_eq_genusFF, ← genusFF_x1FunctionFieldC_eq k M hM, ← hrankΩ]
    let e : k ⊗[ℤ] ↥(Lat M) ≃ₗ[k] Reg k M :=
      LinearMap.linearEquivOfInjective (e0 k M hM) (e0_injective k M hM) hdim
    refine ⟨e, fun c f a ha => ?_⟩
    have he : e (c ⊗ₜ[ℤ] f) = e0 k M hM (c ⊗ₜ[ℤ] f) := rfl
    rw [he, qexp_e0_tmul, coefZ_eq_of_forall f a ha]
    rfl
  · intro ω₁ ω₂ h
    exact Subtype.ext (qExpansionDiffAlong_val_injective k M h)

end Main

end X1OmegaIso
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve.X1OmegaIso"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve.X1OmegaIso P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve.X1OmegaIso P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective.ModularCurve"

open scoped TensorProduct ModularForm MatrixGroups in
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (M : ℕ) [NeZero M] (hM : (M : k) ≠ 0) :
    (∃ e : k ⊗[ℤ] ↥(Submodule.span ℤ
          {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
            ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
              ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈
                Set.range ((↑) : ℤ → ℂ)}) ≃ₗ[k]
        ↥(AlgebraicCurve.regularDifferentials k ↥(ModularCurve.x1FunctionFieldC k M)),
      ∀ (c : k)
        (f : ↥(Submodule.span ℤ
          {f : CuspForm (CongruenceSubgroup.Gamma1 M) 2 |
            ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M → ∀ n : ℕ,
              ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ) n ∈
                Set.range ((↑) : ℤ → ℂ)}))
        (a : ℕ → ℤ),
        (∀ n : ℕ, ModularFormClass.qCoeff
            ((f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) : UpperHalfPlane → ℂ) n = (a n : ℂ)) →
        ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
            (e (c ⊗ₜ[ℤ] f) : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k]) =
          c • HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k))) ∧
    Function.Injective
      (fun ω : ↥(AlgebraicCurve.regularDifferentials k ↥(ModularCurve.x1FunctionFieldC k M)) =>
        ModularCurve.qExpansionDiffAlong (ModularCurve.x1FunctionFieldC k M).val
          (ω : Ω[↥(ModularCurve.x1FunctionFieldC k M)⁄k])) :=
  ModularCurve.X1OmegaIso.main k M hM

end S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective
end P2MW
export P2MW.S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldC_qExpansionDiffAlong_eq_and_injective (solution)
