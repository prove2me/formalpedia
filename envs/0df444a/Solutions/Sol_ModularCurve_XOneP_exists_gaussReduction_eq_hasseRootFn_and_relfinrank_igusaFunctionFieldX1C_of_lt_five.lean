-- Prove2me | solution 1 for ModularCurve.XOneP.exists_gaussReduction_eq_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e30b7ba7-7afc-5c09-8302-56140c5f85c3

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
import Theorems.Thm_ModularForm_exists_gamma1_weightOne_qCoeff_intCast_and_two_dvd_sub_one
import Theorems.Thm_ModularCurve_isKummerGenerator_two_hasseRootFn_of_charP_three
import Theorems.Thm_ModularCurve_exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_hasseRootFn_notMem_x1FunctionFieldC_charThree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_gaussReduction_eq_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C_of_lt_five
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd"
p2m_attr_erase "instance" "KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm MatrixGroups BigOperators

namespace HasseLiftOrthE96

theorem isPrimitive_of_odd_prime {p : ℕ} [hp : Fact p.Prime] (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) :
    χ.IsPrimitive := by
  have hne : χ ≠ 1 := by
    intro h
    rw [h, DirichletCharacter.Odd] at hodd
    have : ((1 : DirichletCharacter ℂ p) (-1 : ZMod p)) = 1 := by
      rw [MulChar.one_apply]; exact (isUnit_one.neg)
    rw [this] at hodd
    norm_num at hodd
  rw [DirichletCharacter.isPrimitive_def]
  rcases hp.out.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with h1 | h2
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) hne
  · exact h2

open Classical in

theorem sum_odd_apply_eq {p : ℕ} [hp : Fact p.Prime] (d : ZMod p) :
    (∑ χ : DirichletCharacter ℂ p, if χ.Odd then χ d else 0)
      = ((p - 1 : ℕ) : ℂ) / 2 * ((if d = 1 then 1 else 0) - (if d = -1 then 1 else 0)) := by

  have key : ∀ χ : DirichletCharacter ℂ p,
      (if χ.Odd then χ d else 0) = (χ d - χ (-d)) / 2 := by
    intro χ
    rcases χ.even_or_odd with he | ho
    · rw [if_neg he.not_odd, he.eval_neg, sub_self, zero_div]
    · rw [if_pos ho, ho.eval_neg]; ring
  simp_rw [key, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [DirichletCharacter.sum_characters_eq, DirichletCharacter.sum_characters_eq]
  have htot : (p.totient : ℂ) = ((p - 1 : ℕ) : ℂ) := by rw [Nat.totient_prime hp.out]
  have hneg : (-d = 1) ↔ (d = -1) := neg_eq_iff_eq_neg
  simp only [htot, hneg]
  split_ifs <;> ring

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have h := CongruenceSubgroup.strictPeriods_Gamma1 p
  change ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods = _ at h
  rw [h]
  exact AddSubgroup.mem_zmultiples 1

def eis (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) : ModularForm (Gamma1 p) 1 :=
  Classical.choose (ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd p χ
    (isPrimitive_of_odd_prime χ hodd) hodd)

theorem eis_qCoeff_zero (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) :
    ModularFormClass.qCoeff (eis p χ hodd) 0 =
      -(∑ a ∈ Finset.range p, (a : ℂ) * χ (a : ZMod p)) / (2 * p) :=
  (Classical.choose_spec (ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd p χ
    (isPrimitive_of_odd_prime χ hodd) hodd)).2.1

theorem eis_qCoeff_pos (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) (n : ℕ) (hn : 0 < n) :
    ModularFormClass.qCoeff (eis p χ hodd) n = ∑ d ∈ n.divisors, χ (d : ZMod p) :=
  (Classical.choose_spec (ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd p χ
    (isPrimitive_of_odd_prime χ hodd) hodd)).2.2 n hn

open Classical in

def term (χ : DirichletCharacter ℂ p) : ModularForm (Gamma1 p) 1 :=
  if h : χ.Odd then eis p χ h else 0

def G0 : ModularForm (Gamma1 p) 1 := ∑ χ : DirichletCharacter ℂ p, term p χ

theorem qExpansion_sum {ι : Type*} (s : Finset ι) {k : ℤ} (F : ι → ModularForm (Gamma1 p) k) :
    UpperHalfPlane.qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, UpperHalfPlane.qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UpperHalfPlane.qExpansion_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
      UpperHalfPlane.qExpansion_add
        (ModularFormClass.analyticAt_cuspFunction_zero (F a) one_pos (one_mem_strictPeriods p))
        (ModularFormClass.analyticAt_cuspFunction_zero (∑ i ∈ s, F i) one_pos (one_mem_strictPeriods p)),
      ih]

open Classical in
theorem coeff_qExpansion_term (χ : DirichletCharacter ℂ p) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑(term p χ))) =
      if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) n else 0 := by
  unfold term
  split_ifs with h
  · rfl
  · simp [UpperHalfPlane.qExpansion_zero]

open Classical in
theorem coeff_qExpansion_G0 (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑(G0 p))) =
      ∑ χ : DirichletCharacter ℂ p, if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) n else 0 := by
  unfold G0
  rw [qExpansion_sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => coeff_qExpansion_term p χ n

end

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

def A (n : ℕ) : ℕ := (n.divisors.filter (fun d : ℕ => ((d : ZMod p)) = 1)).card

def B (n : ℕ) : ℕ := (n.divisors.filter (fun d : ℕ => ((d : ZMod p)) = -1)).card

theorem natCast_zmod_eq_one_iff {a : ℕ} (ha : a < p) : ((a : ZMod p) = 1) ↔ a = 1 := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, ZMod.val_one] at this
  · rintro rfl; simp

theorem natCast_zmod_eq_neg_one_iff {a : ℕ} (ha : a < p) : ((a : ZMod p) = -1) ↔ a = p - 1 := by
  constructor
  · intro h
    have h1 : ((a + 1 : ℕ) : ZMod p) = 0 := by
      push_cast; rw [h]; ring
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : a + 1 = p := by
      obtain ⟨c, hc⟩ := h1
      rcases c with _ | c
      · simp at hc
      · nlinarith [hp.out.pos]
    omega
  · rintro rfl
    have h1 : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hp.out.one_le, ZMod.natCast_self]
    exact eq_neg_of_add_eq_zero_left h1

theorem sum_range_mul_ite_one :
    (∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = 1 then 1 else 0)) = 1 := by
  have : ∀ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = 1 then (1 : ℂ) else 0) =
      if a = 1 then (a : ℂ) else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases h1 : a = 1
    · subst h1; simp
    · have h1' : ¬ ((a : ZMod p) = 1) := fun h => h1 ((natCast_zmod_eq_one_iff p ha).mp h)
      simp [h1, h1']
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr hp.out.one_lt)]
  simp

theorem sum_range_mul_ite_neg_one :
    (∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = -1 then 1 else 0)) = (p : ℂ) - 1 := by
  have : ∀ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = -1 then (1 : ℂ) else 0) =
      if a = p - 1 then (a : ℂ) else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases h1 : a = p - 1
    · subst h1
      have h1' : (((p - 1 : ℕ) : ZMod p) = -1) := (natCast_zmod_eq_neg_one_iff p ha).mpr rfl
      simp [h1']
    · have h1' : ¬ ((a : ZMod p) = -1) := fun h => h1 ((natCast_zmod_eq_neg_one_iff p ha).mp h)
      simp [h1, h1']
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (Nat.sub_lt hp.out.pos one_pos))]
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]

open Classical in

theorem coeff_G0_zero :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (⇑(G0 p))) =
      ((p - 1 : ℕ) : ℂ) * ((p : ℂ) - 2) / (4 * p) := by
  rw [coeff_qExpansion_G0]
  have step1 : ∀ χ : DirichletCharacter ℂ p,
      (if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) 0 else 0) =
        ∑ a ∈ Finset.range p, (-(1 : ℂ) / (2 * p)) * ((a : ℂ) * (if χ.Odd then χ (a : ZMod p) else 0)) := by
    intro χ
    by_cases h : χ.Odd
    · rw [dif_pos h, eis_qCoeff_zero]
      simp only [if_pos h, ← Finset.mul_sum]
      ring
    · rw [dif_neg h]
      symm
      apply Finset.sum_eq_zero
      intro a _
      simp only [if_neg h, mul_zero]
  simp_rw [step1]
  rw [Finset.sum_comm]
  have inner : ∀ a ∈ Finset.range p,
      (∑ χ : DirichletCharacter ℂ p, (-(1 : ℂ) / (2 * p)) * ((a : ℂ) * (if χ.Odd then χ (a : ZMod p) else 0))) =
        (-(1 : ℂ) / (2 * p)) * ((a : ℂ) * (((p - 1 : ℕ) : ℂ) / 2 *
          ((if (a : ZMod p) = 1 then 1 else 0) - (if (a : ZMod p) = -1 then 1 else 0)))) := by
    intro a _
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_odd_apply_eq]
  rw [Finset.sum_congr rfl inner, ← Finset.mul_sum]
  have split : (∑ a ∈ Finset.range p, (a : ℂ) * (((p - 1 : ℕ) : ℂ) / 2 *
      ((if (a : ZMod p) = 1 then (1 : ℂ) else 0) - (if (a : ZMod p) = -1 then 1 else 0)))) =
      ((p - 1 : ℕ) : ℂ) / 2 * ((∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = 1 then (1 : ℂ) else 0)) -
        (∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = -1 then (1 : ℂ) else 0))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [split, sum_range_mul_ite_one, sum_range_mul_ite_neg_one]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  field_simp
  ring

open Classical in

theorem coeff_G0_pos (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑(G0 p))) =
      ((p - 1 : ℕ) : ℂ) / 2 * ((A p n : ℂ) - (B p n : ℂ)) := by
  rw [coeff_qExpansion_G0]
  have step1 : ∀ χ : DirichletCharacter ℂ p,
      (if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) n else 0) =
        ∑ d ∈ n.divisors, (if χ.Odd then χ (d : ZMod p) else 0) := by
    intro χ
    by_cases h : χ.Odd
    · rw [dif_pos h, eis_qCoeff_pos p χ h n hn]
      simp only [if_pos h]
    · rw [dif_neg h]
      symm
      apply Finset.sum_eq_zero
      intro a _
      simp only [if_neg h, mul_zero]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [sum_odd_apply_eq, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [A, B, Finset.sum_boole, Nat.cast_id]

end

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

def G : ModularForm (Gamma1 p) 1 := ((4 * p : ℂ) / ((p : ℂ) - 1)) • G0 p

def pG : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then (p : ℤ) - 2 else 2 * p * ((A p n : ℤ) - (B p n : ℤ))

theorem qExpansion_G : UpperHalfPlane.qExpansion 1 (⇑(G p)) =
    ((4 * p : ℂ) / ((p : ℂ) - 1)) • UpperHalfPlane.qExpansion 1 (⇑(G0 p)) := by
  unfold G
  rw [ModularForm.IsGLPos.coe_smul]
  exact UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero (G0 p) one_pos (one_mem_strictPeriods p)) _

theorem isIntegralQExp_G (hp3 : 3 ≤ p) : ModularCurve.IsIntegralQExp (⇑(G p)) (pG p) := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    have : (p : ℂ) ≠ 1 := by exact_mod_cast (show p ≠ 1 by omega)
    exact sub_ne_zero.mpr this
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hcast : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [qExpansion_G, map_smul, smul_eq_mul]
  unfold pG
  rw [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl, coeff_G0_zero, hcast]
    push_cast
    field_simp
    try ring
  · rw [if_neg hn.ne', coeff_G0_pos p n hn, hcast]
    push_cast
    field_simp
    try ring

def H : ModularForm (Gamma1 p) 0 := (((p : ℂ) - 2)) • (1 : ModularForm (Gamma1 p) 0)

def pH : PowerSeries ℤ := PowerSeries.C ((p : ℤ) - 2)

theorem isIntegralQExp_H : ModularCurve.IsIntegralQExp (⇑(H p)) (pH p) := by
  unfold H pH ModularCurve.IsIntegralQExp
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one,
    UpperHalfPlane.qExpansion_smul (by
      rw [← ModularForm.one_coe_eq_one (Γ := ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))]
      exact ModularFormClass.analyticAt_cuspFunction_zero (1 : ModularForm (Gamma1 p) 0) one_pos
        (one_mem_strictPeriods p)),
    UpperHalfPlane.qExpansion_one, PowerSeries.map_C]
  ext n
  simp [PowerSeries.coeff_C, Algebra.smul_def]

theorem map_pH : (pH p).map (Int.castRingHom (ZMod p)) = PowerSeries.C (-2 : ZMod p) := by
  unfold pH
  rw [PowerSeries.map_C]
  congr 1
  simp

theorem map_pH_ne_zero (hp3 : 3 ≤ p) : (pH p).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  rw [map_pH]
  intro h
  have h2 : (-2 : ZMod p) = 0 := by
    have := congrArg (PowerSeries.coeff 0) h
    simpa using this
  have h2' : ((2 : ℕ) : ZMod p) = 0 := by
    have := congrArg Neg.neg h2
    simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h2'
  have := Nat.le_of_dvd two_pos h2'
  omega

theorem map_pG (hp3 : 3 ≤ p) : (pG p).map (Int.castRingHom (ZMod p)) = PowerSeries.C (-2 : ZMod p) := by
  ext n
  unfold pG
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  split_ifs with h
  · simp
  · push_cast
    simp [ZMod.natCast_self]

end

end HasseLiftOrthE96

p2m_open "CongruenceSubgroup ModularCurve~coeffMap_injective"
open scoped MatrixGroups ModularForm

noncomputable section

namespace S1cAux

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [CharZero L] (q : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ q) = HahnSeries.ofPowerSeries ℤ L (q.map (Int.castRingHom L)) := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · simp
  · simp

theorem map_intCast_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (q : PowerSeries ℤ) :
    (q.map (Int.castRingHom A)).map φ = q.map (Int.castRingHom B) := by
  have h : φ.comp (Int.castRingHom A) = Int.castRingHom B := RingHom.ext_int _ _
  rw [← h, PowerSeries.map_comp, RingHom.comp_apply]

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · exact (by rw [Gamma1_mem]; simp [ModularGroup.coe_T] : ModularGroup.T ∈ Gamma1 N)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem exists_ratio_presentation
    (p : ℕ) (M : ℕ) [NeZero (M * p)]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = laurentBaseChange L (x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    {k : ℤ} (f g : ModularForm ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC (IsLocalRing.ResidueField A) pg ≠ 0) :
    ∃ F : ↥K,
      (pg.map (Int.castRingHom A)).map (IsLocalRing.residue A) ≠ 0 ∧
      (F : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((pg.map (Int.castRingHom A)).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L ((pf.map (Int.castRingHom A)).map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((pf.map (Int.castRingHom A)).map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((pg.map (Int.castRingHom A)).map (IsLocalRing.residue A))
        = intSeriesC (IsLocalRing.ResidueField A) pf / intSeriesC (IsLocalRing.ResidueField A) pg := by
  have hpg0 : pg ≠ 0 := by
    rintro rfl; exact hg0 (by rw [intSeriesC_zero])
  have hgQ : intSeriesC ℚ pg ≠ 0 := by
    intro h
    apply hpg0
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_zero]
    exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero (HahnSeries.ofPowerSeries ℤ ℚ)).symm)
  have hmem : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ x1FunctionField (M * p) :=
    div_mem_qExpFunctionFieldC f g hf hg hgQ
  have hFK : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ K := by
    rw [hK]; exact coeffEmb_mem_laurentBaseChange L hmem
  refine ⟨⟨_, hFK⟩, ?_, ?_, ?_⟩
  · rw [map_intCast_map]; exact fun h => hg0 (by rw [intSeriesC, h, map_zero])
  · rw [map_intCast_map, map_intCast_map]
    show coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) * _ = _
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    have hne : HahnSeries.ofPowerSeries ℤ L (pg.map (Int.castRingHom L)) ≠ 0 := by
      intro h
      apply hpg0
      apply PowerSeries.map_injective (Int.castRingHom L) Int.cast_injective
      rw [map_zero]
      exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero (HahnSeries.ofPowerSeries ℤ L)).symm)
    rw [div_mul_cancel₀ _ hne]
  · rw [map_intCast_map, map_intCast_map]; rfl

end S1cAux

end

namespace SmallPAux

p2m_open "CongruenceSubgroup ModularCurve~coeffMap_injective ModularForm"
open scoped MatrixGroups ModularForm

theorem weightShift_three :
    ∃ (k : ℤ) (G : ModularForm (Gamma1 3) (k + 1)) (H : ModularForm (Gamma1 3) k)
      (pG pH : PowerSeries ℤ),
      IsIntegralQExp G pG ∧ IsIntegralQExp H pH ∧
      pH.map (Int.castRingHom (ZMod 3)) ≠ 0 ∧
      pG.map (Int.castRingHom (ZMod 3)) = pH.map (Int.castRingHom (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨0, HasseLiftOrthE96.G 3, HasseLiftOrthE96.H 3, HasseLiftOrthE96.pG 3, HasseLiftOrthE96.pH 3,
    HasseLiftOrthE96.isIntegralQExp_G 3 le_rfl, HasseLiftOrthE96.isIntegralQExp_H 3,
    HasseLiftOrthE96.map_pH_ne_zero 3 le_rfl, ?_⟩
  rw [HasseLiftOrthE96.map_pG 3 le_rfl, HasseLiftOrthE96.map_pH]

theorem coeffMap_intSeriesC {κ κ' : Type*} [Field κ] [Field κ'] (σ : κ →+* κ') (s : PowerSeries ℤ) :
    coeffMap σ (intSeriesC κ s) = intSeriesC κ' s := by
  ext n
  rw [coeffMap_coeff, intSeriesC, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · simp
  · rw [PowerSeries.coeff_map, PowerSeries.coeff_map]; simp

theorem coeffMap_injective {κ κ' : Type*} [Field κ] [Field κ'] (σ : κ →+* κ') :
    Function.Injective (coeffMap σ) := by
  intro x y h
  ext n
  have := congrArg (fun z => HahnSeries.coeff z n) h
  simp only [coeffMap_coeff] at this
  exact σ.injective this

end SmallPAux

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "CongruenceSubgroup ModularCurve~coeffMap_injective"
open scoped MatrixGroups ModularForm

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M)
    (hp : p < 5) :
    (∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
        = w.hasseRootFn) ∧
    IntermediateField.relfinrank (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M)
      (ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) = p - 1 := by
  classical
  haveI hpr : Fact p.Prime := inferInstance
  haveI : NeZero p := ⟨hpr.out.ne_zero⟩
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩

  have hpκ : (p : (IsLocalRing.ResidueField A)) = 0 := by
    rw [← map_natCast (algebraMap A (IsLocalRing.ResidueField A)) p]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hAp
  haveI : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero hpr.out).mpr hpκ
  have hZκ : (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
  have hmapκ : ∀ s : PowerSeries ℤ, s.map (Int.castRingHom (IsLocalRing.ResidueField A)) =
      (s.map (Int.castRingHom (ZMod p))).map (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) := by
    intro s; rw [← hZκ, PowerSeries.map_comp, RingHom.comp_apply]

  have hcongr : ∀ s t : PowerSeries ℤ, s.map (Int.castRingHom (ZMod p)) = t.map (Int.castRingHom (ZMod p)) →
      intSeriesC (IsLocalRing.ResidueField A) s = intSeriesC (IsLocalRing.ResidueField A) t := by
    intro s t h; rw [intSeriesC, intSeriesC, hmapκ, hmapκ t, h]
  have hleM : ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_right M p))
  have hlep : ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_left p M))
  have hw0 := w.intSeriesC_ne_zero

  have hp23 : p = 2 ∨ p = 3 := by
    have h2 := hpr.out.two_le
    interval_cases p
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hpr.out (by decide)

  have hK₀Ig : x1FunctionFieldC (IsLocalRing.ResidueField A) M ≤ igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w :=
    x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w
  rcases hp23 with rfl | rfl
  ·

    have h2M : ¬ 2 ∣ M := hpM
    obtain ⟨U, b, hUb, hb0, hbpos⟩ :=
      ModularForm.exists_gamma1_weightOne_qCoeff_intCast_and_two_dvd_sub_one M (by omega) h2M
    set pU : PowerSeries ℤ := PowerSeries.mk b with hpUdef
    have hU : IsIntegralQExp (⇑U) pU := by
      rw [ModularCurve.isIntegralQExp_iff]
      intro n
      rw [hpUdef, PowerSeries.coeff_mk]
      exact (hUb n).symm
    have hŪ : intSeriesC (IsLocalRing.ResidueField A) pU = 1 := by
      have h2 : (2 : IsLocalRing.ResidueField A) = 0 := by exact_mod_cast hpκ
      have hcast : ∀ n : ℕ, ((b n : ℤ) : IsLocalRing.ResidueField A) = if n = 0 then 1 else 0 := by
        intro n
        split_ifs with hn
        · subst hn
          obtain ⟨c, hc⟩ := hb0
          have : b 0 = 2 * c + 1 := by omega
          rw [this]; push_cast; rw [h2]; ring
        · obtain ⟨c, hc⟩ := hbpos n (Nat.pos_of_ne_zero hn)
          rw [hc]; push_cast; rw [h2]; ring
      rw [intSeriesC]
      have : pU.map (Int.castRingHom (IsLocalRing.ResidueField A)) = 1 := by
        ext n
        rw [PowerSeries.coeff_map, hpUdef, PowerSeries.coeff_mk, eq_intCast, hcast, PowerSeries.coeff_one]
      rw [this, map_one]
    have ha : w.hasseRootFn = intSeriesC (IsLocalRing.ResidueField A) pU / intSeriesC (IsLocalRing.ResidueField A) w.series := by
      rw [IntegralWeightOneForm.hasseRootFn, hŪ, one_div]
    refine ⟨?_, ?_⟩
    · obtain ⟨F, hy, hpres, hred⟩ :=
        S1cAux.exists_ratio_presentation 2 M L K hK A (restrictForm hleM U) (restrictForm hleM w.form)
          pU w.series hU w.isIntegralQExp hw0
      exact ⟨F, _, _, hy, hpres, by rw [hred, ha]⟩
    ·
      have haK₀ : w.hasseRootFn ∈ x1FunctionFieldC (IsLocalRing.ResidueField A) M := by
        rw [ha, x1FunctionFieldC]
        exact div_mem_qExpFunctionFieldC U w.form hU w.isIntegralQExp hw0
      show IntermediateField.relfinrank _ _ = 2 - 1
      rw [show (2 : ℕ) - 1 = 1 from rfl, IntermediateField.relfinrank_eq_one_iff, igusaFunctionFieldX1C,
        IgusaCover.igusaFunctionField, IntermediateField.adjoin_le_iff]
      rintro z (hz | hz)
      · exact hz
      · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact haK₀
  ·
    obtain ⟨k, G, H, pG, pH, hG, hH, hH0, hGH⟩ := SmallPAux.weightShift_three
    have hκH : intSeriesC (IsLocalRing.ResidueField A) pH ≠ 0 := by
      intro h0
      apply hH0
      apply PowerSeries.map_injective (ZMod.castHom (dvd_refl 3) (IsLocalRing.ResidueField A))
        (ZMod.castHom (dvd_refl 3) (IsLocalRing.ResidueField A)).injective
      rw [map_zero, ← hmapκ]
      exact HahnSeries.ofPowerSeries_injective
        (h0.trans (map_zero (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A))).symm)
    have hGH' : intSeriesC (IsLocalRing.ResidueField A) pG = intSeriesC (IsLocalRing.ResidueField A) pH :=
      hcongr _ _ hGH
    have hden : IsIntegralQExp (⇑((restrictForm hlep H).mul (restrictForm hleM w.form))) (pH * w.series) := by
      rw [IsIntegralQExp, map_mul, ModularForm.coe_mul]
      have h1 : (pH.map (Int.castRingHom ℂ)) = UpperHalfPlane.qExpansion 1 (⇑(restrictForm hlep H)) := hH
      have h2 : (w.series.map (Int.castRingHom ℂ)) =
          UpperHalfPlane.qExpansion 1 (⇑(restrictForm hleM w.form)) := w.isIntegralQExp
      rw [h1, h2]
      exact (ModularForm.qExpansion_mul_coe one_pos (S1cAux.one_mem_strictPeriods_Gamma1 (M * 3)) _ _).symm
    have hden0 : intSeriesC (IsLocalRing.ResidueField A) (pH * w.series) ≠ 0 := by
      rw [intSeriesC_mul]; exact mul_ne_zero hκH hw0
    refine ⟨?_, ?_⟩
    · obtain ⟨F, hy, hpres, hred⟩ :=
        S1cAux.exists_ratio_presentation 3 M L K hK A (restrictForm hlep G)
          ((restrictForm hlep H).mul (restrictForm hleM w.form)) pG (pH * w.series) hG hden hden0
      refine ⟨F, _, _, hy, hpres, ?_⟩
      rw [hred, intSeriesC_mul, hGH', IntegralWeightOneForm.hasseRootFn, div_mul_cancel_left₀ hκH]
    ·
      set κ := IsLocalRing.ResidueField A with hκdef
      set a : LaurentSeries κ := w.hasseRootFn with hadef

      have ha2K₀ : a ^ 2 ∈ x1FunctionFieldC (IsLocalRing.ResidueField A) M :=
        (ModularCurve.isKummerGenerator_two_hasseRootFn_of_charP_three κ M w).pow_mem

      have haK₀ : a ∉ x1FunctionFieldC (IsLocalRing.ResidueField A) M := by
        intro haK
        let κ' := AlgebraicClosure κ
        let σ : κ →+* κ' := algebraMap κ κ'
        obtain ⟨ι, hι⟩ := ModularCurve.exists_ringHom_qExpFunctionFieldC_coe_eq_coeffMap σ (Gamma1 M)
        have hσw : intSeriesC κ' w.series ≠ 0 := by
          rw [← SmallPAux.coeffMap_intSeriesC σ]; intro h
          exact hw0 (SmallPAux.coeffMap_injective σ (h.trans (map_zero _).symm))
        let w' : IntegralWeightOneForm κ' M :=
          { form := w.form, series := w.series, isIntegralQExp := w.isIntegralQExp, intSeriesC_ne_zero := hσw }
        have hmem : coeffMap σ a ∈ x1FunctionFieldC κ' M := by
          have := (ι ⟨a, haK⟩).2
          rw [x1FunctionFieldC]
          convert this using 1
          exact (hι ⟨a, haK⟩).symm
        have heq : coeffMap σ a = w'.hasseRootFn := by
          rw [hadef, IntegralWeightOneForm.hasseRootFn, IntegralWeightOneForm.hasseRootFn, map_inv₀,
            SmallPAux.coeffMap_intSeriesC]
        rw [heq] at hmem
        exact ModularCurve.hasseRootFn_notMem_x1FunctionFieldC_charThree M hM hpM κ' w' hmem

      have haev : Polynomial.aeval a (Polynomial.X ^ 2 - Polynomial.C (⟨a ^ 2, ha2K₀⟩ : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M))) = 0 := by
        rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
        exact sub_eq_zero.mpr rfl
      have hint : IsIntegral ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) a := by
        refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨a ^ 2, ha2K₀⟩, ?_, ?_⟩
        · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
        · rw [← Polynomial.aeval_def]; exact haev
      have hdeg : (minpoly ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) a).natDegree = 2 := by
        apply le_antisymm
        · have hq0 : (Polynomial.X ^ 2 - Polynomial.C (⟨a ^ 2, ha2K₀⟩ : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M))) ≠ 0 :=
            (Polynomial.monic_X_pow_sub_C _ two_ne_zero).ne_zero
          have := Polynomial.natDegree_le_of_dvd (minpoly.dvd _ a haev) hq0
          rwa [Polynomial.natDegree_X_pow_sub_C] at this
        · rw [minpoly.two_le_natDegree_iff hint]
          rintro ⟨y, hy⟩
          exact haK₀ (hy ▸ y.2)
      show IntermediateField.relfinrank _ _ = 3 - 1
      rw [show (3 : ℕ) - 1 = 2 from rfl, IntermediateField.relfinrank_eq_finrank_of_le hK₀Ig]
      have hIg : igusaFunctionFieldX1C κ M w = IntermediateField.adjoin κ ((x1FunctionFieldC (IsLocalRing.ResidueField A) M : Set (LaurentSeries κ)) ∪ {a}) := rfl
      have hext : IntermediateField.extendScalars hK₀Ig =
          IntermediateField.adjoin ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M)
            ((x1FunctionFieldC (IsLocalRing.ResidueField A) M : Set (LaurentSeries κ)) ∪ {a}) :=
        IntermediateField.extendScalars_adjoin hK₀Ig
      have hadj : IntermediateField.adjoin ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M)
            ((x1FunctionFieldC (IsLocalRing.ResidueField A) M : Set (LaurentSeries κ)) ∪ {a}) =
          IntermediateField.adjoin ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) {a} := by
        apply le_antisymm
        · rw [IntermediateField.adjoin_le_iff]
          rintro z (hz | hz)
          · exact IntermediateField.algebraMap_mem
              (IntermediateField.adjoin ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M) {a}) (⟨z, hz⟩ : ↥(x1FunctionFieldC (IsLocalRing.ResidueField A) M))
          · rw [Set.mem_singleton_iff] at hz
            rw [hz]; exact IntermediateField.mem_adjoin_simple_self _ a
        · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
      rw [hext, hadj, IntermediateField.adjoin.finrank hint, hdeg]

end S_ModularCurve_XOneP_exists_gaussReduction_eq_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C_of_lt_five
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_gaussReduction_eq_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C_of_lt_five (solution)
