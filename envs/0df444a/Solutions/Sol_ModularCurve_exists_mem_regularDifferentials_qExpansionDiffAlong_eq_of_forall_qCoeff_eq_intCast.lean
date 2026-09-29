-- Prove2me | solution 1 for ModularCurve.exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1144bd10-5d17-5283-8420-4ee33d3691bd

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials
import Theorems.Thm_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
import Theorems.Thm_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion
import Theorems.Thm_ModularCurve_mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.cuspCount_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "ModularCurve~coeffMap_injective P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve AlgebraicCurve KaehlerDifferential HahnSeries"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldC ofPowerSeries_coeff_of_neg thetaL thetaL_apply qExpansionDiffAlong coeffMap coeffMap_coeff qEuler qEuler_coeff diffQExp diffQExp_D diffQExpBar regularDifferentialsBar modularFunctionFieldBar coeffMap_ofPowerSeries exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast exists_coeffMap_diffQExpBar_eq_qExpansion mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC modularFunctionFieldC_eq_modularFunctionFieldFullC qExpansionDiffAlong_D qExpansionDiffAlong_smul"
namespace Omega2AssemblyProof
p2m_open "ModularCurve~coeffMap_injective"

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

theorem coeffMap_ofPowerSeries (g : PowerSeries R) :
    coeffMap φ (ofPowerSeries ℤ R g) = ofPowerSeries ℤ S (g.map φ) := by
  ext d
  rw [coeffMap_coeff]
  rcases le_or_gt 0 d with hd | hd
  · lift d to ℕ using hd
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hd, ofPowerSeries_coeff_of_neg _ hd, map_zero]

theorem coeffMap_ofPowerSeries_intCast (a : ℕ → ℤ) :
    coeffMap φ (ofPowerSeries ℤ R (PowerSeries.mk fun n => (a n : R))) =
      ofPowerSeries ℤ S (PowerSeries.mk fun n => (a n : S)) := by
  rw [coeffMap_ofPowerSeries]
  congr 1
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_intCast]

theorem coeffMap_injective {K L : Type*} [Field K] [Field L] (ψ : K →+* L) :
    Function.Injective (coeffMap ψ) := by
  intro x y h
  ext d
  have := congrArg (fun z : LaurentSeries L => z.coeff d) h
  simp only [coeffMap_coeff] at this
  exact ψ.injective this

end CoeffMap

section Theta

variable {L : Type*} [Field L]

theorem thetaL_eq_qEuler (x : LaurentSeries L) : thetaL L x = qEuler L x := by
  ext n
  rw [thetaL_apply, coeff_single_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, qEuler_coeff, Nat.cast_one, sub_add_cancel,
    Ring.choose_one_right, one_mul, zsmul_eq_mul]

variable (E : IntermediateField L (LaurentSeries L))

local notation "qE" => qExpansionDiffAlong (IntermediateField.val E)

theorem qE_add (η η' : Ω[E⁄L]) : qE (η + η') = qE η + qE η' := map_add _ _ _

theorem qE_zero : qE (0 : Ω[E⁄L]) = 0 := map_zero _

theorem diffQExp_add (η η' : Ω[E⁄L]) : diffQExp E (η + η') = diffQExp E η + diffQExp E η' :=
  map_add _ _ _

theorem diffQExp_zero : diffQExp E (0 : Ω[E⁄L]) = 0 := map_zero _

theorem qE_D (x : E) : qE (D L E x) = thetaL L (x : LaurentSeries L) := qExpansionDiffAlong_D _ x

theorem qE_smul (g : E) (η : Ω[E⁄L]) : qE (g • η) = (g : LaurentSeries L) * qE η :=
  qExpansionDiffAlong_smul _ g η

theorem qExpansionDiffAlong_val_eq_diffQExp (η : Ω[E⁄L]) : qE η = diffQExp E η := by
  have hη : η ∈ Submodule.span E (Set.range (D L E)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hη using Submodule.span_induction with
  | mem ω hω =>
      obtain ⟨x, rfl⟩ := hω
      rw [qE_D, diffQExp_D, thetaL_eq_qEuler]
  | zero => rw [qE_zero, diffQExp_zero]
  | add ω ω' _ _ h h' => rw [qE_add, diffQExp_add, h, h']
  | smul g ω _ h =>
      rw [qE_smul, map_smul, h]
      rfl

end Theta

section CharZeroBase

local notation "ℚbar" => AlgebraicClosure ℚ

scoped instance isAlgebraic_rat_bar : Algebra.IsAlgebraic ℚ ℚbar := AlgebraicClosure.isAlgebraic ℚ

def iotaC : ℚbar →+* ℂ :=
  (IsAlgClosed.lift (R := ℚ) (S := ℚbar) (M := ℂ)).toRingHom

theorem modularFunctionFieldC_eq_bar (N : ℕ) [NeZero N] :
    modularFunctionFieldC ℚbar N = modularFunctionFieldBar N := by
  have h0 : ¬ (0 : ℕ) ∣ N := by
    rw [zero_dvd_iff]; exact NeZero.ne N
  rw [modularFunctionFieldC_eq_modularFunctionFieldFullC ℚbar 0 N h0]
  exact (laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚbar N).symm

theorem charZero_base (N : ℕ) [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ ω ∈ regularDifferentials ℚbar (modularFunctionFieldC ℚbar N),
      qExpansionDiffAlong (modularFunctionFieldC ℚbar N).val ω =
        ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) := by

  have hf : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ iotaC.range := fun n =>
    ⟨(a n : ℚbar), by rw [map_intCast, ha]⟩
  obtain ⟨ω, hω⟩ := exists_coeffMap_diffQExpBar_eq_qExpansion N iotaC f hf
  have hreg : ω ∈ regularDifferentialsBar N :=
    mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion N iotaC f ω hω

  have hq : diffQExpBar N ω = ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) := by
    apply coeffMap_injective iotaC
    rw [hω, coeffMap_ofPowerSeries_intCast]
    congr 1
    ext n
    rw [PowerSeries.coeff_mk, ← ha n]
    rfl
  have hq' : qExpansionDiffAlong (modularFunctionFieldBar N).val ω =
      ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) := by
    rw [qExpansionDiffAlong_val_eq_diffQExp]; exact hq

  suffices key : ∀ E : IntermediateField ℚbar (LaurentSeries ℚbar), E = modularFunctionFieldBar N →
      ∃ ω ∈ regularDifferentials ℚbar E,
        qExpansionDiffAlong E.val ω =
          ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) from
    key _ (modularFunctionFieldC_eq_bar N)
  rintro E rfl
  exact ⟨ω, hreg, hq'⟩

end CharZeroBase

section Residue

local notation "ℚbar" => AlgebraicClosure ℚ

open IsLocalRing Polynomial

theorem isAlgebraic_residueField (p : ℕ) [Fact p.Prime] (A : ValuationSubring ℚbar)
    [CharP (ResidueField A) p] :
    letI : Algebra (ZMod p) (ResidueField A) := ZMod.algebra _ p
    Algebra.IsAlgebraic (ZMod p) (ResidueField A) := by
  letI : Algebra (ZMod p) (ResidueField A) := ZMod.algebra _ p
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x

  have hyalg : IsAlgebraic ℚ (y : ℚbar) := Algebra.IsAlgebraic.isAlgebraic _
  rw [← IsFractionRing.isAlgebraic_iff ℤ ℚ ℚbar] at hyalg
  obtain ⟨P₀, hP₀, hP₀y⟩ := hyalg

  set P₁ : ℤ[X] := P₀.primPart with hP₁
  have hprim : P₁.IsPrimitive := P₀.isPrimitive_primPart
  have hP₁y : eval₂ (Int.castRingHom ℚbar) (y : ℚbar) P₁ = 0 := by
    refine eval₂_primPart_eq_zero (f := Int.castRingHom ℚbar) (RingHom.injective_int _) hP₀ ?_
    exact hP₀y
  have hP₁A : eval₂ (Int.castRingHom A) y P₁ = 0 := by
    apply (FaithfulSMul.algebraMap_injective A ℚbar)
    rw [hom_eval₂, map_zero]
    rw [show (algebraMap A ℚbar).comp (Int.castRingHom A) = Int.castRingHom ℚbar from
      RingHom.ext_int _ _]
    exact hP₁y

  refine ⟨P₁.map (Int.castRingHom (ZMod p)), ?_, ?_⟩
  · intro hzero
    have hdvd : Polynomial.C (p : ℤ) ∣ P₁ := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have hi : (Int.castRingHom (ZMod p)) (P₁.coeff i) = 0 := by
        rw [← coeff_map, hzero, Polynomial.coeff_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hi
    have hunit : IsUnit (p : ℤ) := isPrimitive_iff_isUnit_of_C_dvd.mp hprim _ hdvd
    have hp1 : p = 1 := by
      have := Int.isUnit_iff_natAbs_eq.mp hunit
      rwa [Int.natAbs_natCast] at this
    exact (Fact.out : p.Prime).ne_one hp1
  · rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap (ZMod p) (ResidueField A)).comp (Int.castRingHom (ZMod p)) =
        (residue A).comp (Int.castRingHom A) := RingHom.ext_int _ _
    rw [hcomp, ← hom_eval₂, hP₁A, map_zero]

theorem exists_ringHom_residueField (p : ℕ) [Fact p.Prime] (A : ValuationSubring ℚbar)
    [CharP (ResidueField A) p] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] :
    Nonempty (ResidueField A →+* k) := by
  letI : Algebra (ZMod p) (ResidueField A) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI := isAlgebraic_residueField p A
  exact ⟨(IsAlgClosed.lift (R := ZMod p) (S := ResidueField A) (M := k)).toRingHom⟩

end Residue

theorem main (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ ω ∈ regularDifferentials k (modularFunctionFieldC k N),
      qExpansionDiffAlong (modularFunctionFieldC k N).val ω =
        ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k)) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  ·
    haveI : Fact p.Prime := ⟨hprime⟩
    have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff k p N).mpr h)
    obtain ⟨A, hA⟩ :=
      ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hprime⟩
    haveI : CharP (IsLocalRing.ResidueField A) p :=
      ValuationSubring.residueField_charP_of_liesOverPrime A hprime hA
    obtain ⟨ι⟩ := exists_ringHom_residueField p A k
    obtain ⟨ω₀, hω₀, hq₀⟩ :=
      exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
        p N hpN A hA f a ha
    obtain ⟨ω, hω, hq⟩ :=
      exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials
        ι N hN ω₀ hω₀
    exact ⟨ω, hω, by rw [hq, hq₀, coeffMap_ofPowerSeries_intCast]⟩
  ·
    haveI : CharZero k := CharP.charP_to_charZero k
    let ι : AlgebraicClosure ℚ →+* k :=
      (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := k)).toRingHom
    obtain ⟨ω₀, hω₀, hq₀⟩ := charZero_base N f a ha
    obtain ⟨ω, hω, hq⟩ :=
      exists_mem_regularDifferentials_qExpansionDiffAlong_eq_coeffMap_of_mem_regularDifferentials
        ι N hN ω₀ hω₀
    exact ⟨ω, hω, by rw [hq, hq₀, coeffMap_ofPowerSeries_intCast]⟩

end ModularCurve.Omega2AssemblyProof
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve.Omega2AssemblyProof"
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve"

p2m_open "ModularCurve~coeffMap_injective" in open _root_.P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve AlgebraicCurve in
theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ ω ∈ regularDifferentials k (modularFunctionFieldC k N),
      qExpansionDiffAlong (modularFunctionFieldC k N).val ω =
        HahnSeries.ofPowerSeries ℤ k (PowerSeries.mk fun n => (a n : k)) :=
  ModularCurve.Omega2AssemblyProof.main k N hN f a ha

end
end S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
end P2MW
export P2MW.S_ModularCurve_exists_mem_regularDifferentials_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast (solution)
