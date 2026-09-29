-- Prove2me | solution 1 for ModularCurve.exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/357c33f6-7374-5bf2-885a-ec55b0200e94

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
import Theorems.Thm_ModularCurve_exists_coeffMap_diffQExpBar_eq_qExpansion
import Theorems.Thm_ModularCurve_mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion
import Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_isSeparable_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.cuspCount_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

p2m_open "ModularCurve~coeffEmb_jq~coeffMap_injective P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve AlgebraicCurve KaehlerDifferential HahnSeries IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqModC_rat map_jqModC modularFunctionFieldC jq ofPowerSeries_coeff_of_neg thetaL qExpansionDiffAlong coeffMap coeffMap_coeff coeffEmb coeffEmb_mem_laurentBaseChange jq_mem_full qEuler qEuler_coeff diffQExp_smul_D diffQExpBar regularDifferentialsBar modularFunctionFieldBar coeffMap_ofPowerSeries coeff_jqModC_of_lt modularFunctionFieldFullC coeff_jqModC_neg_one smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar exists_coeffMap_diffQExpBar_eq_qExpansion mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd modularFunctionFieldC_eq_modularFunctionFieldFullC qExpansionDiffAlong_D qExpansionDiffAlong_smul isSeparable_adjoin_coeffEmb_jq_full transcendental_coeffEmb_jq"
namespace Omega2ResidueProof
p2m_open "ModularCurve~coeffEmb_jq~coeffMap_injective"

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

theorem coeffMap_injective (hφ : Function.Injective φ) : Function.Injective (coeffMap φ) := by
  intro x y h
  ext d
  have := congrArg (fun z : LaurentSeries S => z.coeff d) h
  simp only [coeffMap_coeff] at this
  exact hφ this

def thetaR (w : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w

theorem thetaR_coeff (w : LaurentSeries R) (n : ℤ) : (thetaR w).coeff n = (n : R) * w.coeff n := by
  rw [thetaR, coeff_single_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    Nat.cast_one, sub_add_cancel, Ring.choose_one_right, one_mul, zsmul_eq_mul]

theorem coeffMap_thetaR (w : LaurentSeries R) : coeffMap φ (thetaR w) = thetaR (coeffMap φ w) := by
  ext n
  rw [coeffMap_coeff, thetaR_coeff, thetaR_coeff, map_mul, map_intCast, coeffMap_coeff]

theorem thetaL_eq_thetaR {L : Type*} [Field L] (w : LaurentSeries L) : thetaL L w = thetaR w := rfl

end CoeffMap

section ThetaJ

def thetaJInt : LaurentSeries ℤ := thetaR (jqModC ℤ)

theorem coeff_jqModC_of_lt (K : Type*) [CommRing K] {n : ℤ} (hn : n < -1) :
    (jqModC K).coeff n = 0 := by
  rw [jqModC, coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

theorem thetaJInt_coeff_neg_one : thetaJInt.coeff (-1) = -1 := by
  rw [thetaJInt, thetaR_coeff, coeff_jqModC_neg_one]; simp

theorem thetaJInt_coeff_of_lt {n : ℤ} (hn : n < -1) : thetaJInt.coeff n = 0 := by
  rw [thetaJInt, thetaR_coeff, coeff_jqModC_of_lt ℤ hn, mul_zero]

theorem thetaJInt_ne_zero : thetaJInt ≠ 0 := by
  intro h
  have := thetaJInt_coeff_neg_one
  rw [h, HahnSeries.coeff_zero] at this
  exact absurd this (by norm_num)

theorem order_thetaJInt : thetaJInt.order = -1 := by
  refine le_antisymm (order_le_of_coeff_ne_zero (by rw [thetaJInt_coeff_neg_one]; norm_num)) ?_
  by_contra h
  push Not at h
  exact (mt coeff_order_eq_zero.mp thetaJInt_ne_zero) (thetaJInt_coeff_of_lt h)

theorem isUnit_thetaJInt : IsUnit thetaJInt := by
  rw [HahnSeries.isUnit_iff, leadingCoeff_eq, order_thetaJInt, thetaJInt_coeff_neg_one]
  exact isUnit_one.neg

theorem exists_coeffMap_int_eq {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (x : LaurentSeries S) (a : ℕ → ℤ)
    (hx : x * thetaR (jqModC S) = ofPowerSeries ℤ S (PowerSeries.mk fun n => (a n : S))) :
    ∃ z : LaurentSeries ℤ, coeffMap (Int.castRingHom S) z = x := by
  obtain ⟨u, hu⟩ := isUnit_thetaJInt
  set P : LaurentSeries ℤ := ofPowerSeries ℤ ℤ (PowerSeries.mk fun n => a n) with hP
  refine ⟨P * (u⁻¹ : (LaurentSeries ℤ)ˣ), ?_⟩
  have hθ : coeffMap (Int.castRingHom S) thetaJInt = thetaR (jqModC S) := by
    rw [thetaJInt, coeffMap_thetaR]
    congr 1
    exact map_jqModC _
  have hθ0 : thetaR (jqModC S) ≠ 0 := by
    rw [← hθ, ← hu]
    exact (RingHom.isUnit_map _ u.isUnit).ne_zero
  apply mul_right_cancel₀ hθ0
  have hPu : P * (u⁻¹ : (LaurentSeries ℤ)ˣ) * thetaJInt = P := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  have hPS : coeffMap (Int.castRingHom S) P =
      ofPowerSeries ℤ S (PowerSeries.mk fun n => (a n : S)) := by
    have := coeffMap_ofPowerSeries_intCast (R := ℤ) (Int.castRingHom S) a
    simp only [Int.cast_id] at this
    exact this
  rw [hx, ← hθ, ← map_mul, hPu, hPS]

end ThetaJ

section Lift

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_coeffMap_subtype_eq (x : LaurentSeries L) (hx : ∀ n, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, x.isPWO_support.mono ?_⟩, ?_⟩
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    rw [HahnSeries.mem_support]
    exact fun h => hn (Subtype.ext h)
  · ext n
    rfl

theorem exists_coeffMap_subtype_eq_of_int (z : LaurentSeries ℤ) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = coeffMap (Int.castRingHom L) z := by
  apply exists_coeffMap_subtype_eq
  intro n
  rw [coeffMap_coeff]
  exact intCast_mem A _

end Lift

section Bar

local notation "ℚbar" => AlgebraicClosure ℚ

scoped instance isAlgebraic_rat_bar : Algebra.IsAlgebraic ℚ ℚbar := AlgebraicClosure.isAlgebraic ℚ

def iotaC : ℚbar →+* ℂ :=
  (IsAlgClosed.lift (R := ℚ) (S := ℚbar) (M := ℂ)).toRingHom

theorem thetaL_eq_qEuler {L : Type*} [Field L] (x : LaurentSeries L) : thetaL L x = qEuler L x := by
  ext n
  rw [thetaL_eq_thetaR, thetaR_coeff, qEuler_coeff]

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

variable (N : ℕ) [NeZero N]

def J : modularFunctionFieldBar N :=
  ⟨coeffEmb ℚbar jq, coeffEmb_mem_laurentBaseChange ℚbar (jq_mem_full N)⟩

theorem coe_J : ((J N : modularFunctionFieldBar N) : LaurentSeries ℚbar) = jqModC ℚbar :=
  coeffEmb_jq ℚbar

theorem exists_integral_coefficient (A : ValuationSubring ℚbar)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ((⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) •
          D ℚbar (modularFunctionFieldBar N) (J N)) ∈ regularDifferentialsBar N ∧
      coeffMap A.subtype y * thetaR (jqModC ℚbar) =
        ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) := by

  have hf : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ iotaC.range := fun n =>
    ⟨(a n : ℚbar), by rw [map_intCast, ha]⟩
  obtain ⟨ω, hω⟩ := exists_coeffMap_diffQExpBar_eq_qExpansion N iotaC f hf
  have hreg : ω ∈ regularDifferentialsBar N :=
    mem_regularDifferentialsBar_of_coeffMap_diffQExpBar_eq_qExpansion N iotaC f ω hω
  have hq : diffQExpBar N ω = ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) := by
    apply coeffMap_injective iotaC iotaC.injective
    rw [hω, coeffMap_ofPowerSeries_intCast]
    congr 1
    ext n
    rw [PowerSeries.coeff_mk, ← ha n]
    rfl

  haveI : Algebra.IsSeparable (IntermediateField.adjoin ℚbar ({J N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) := isSeparable_adjoin_coeffEmb_jq_full ℚbar N
  obtain ⟨x, hx, -⟩ :=
    KaehlerDifferential.exists_unique_smul_D_of_transcendental ℚbar (J N)
      (transcendental_coeffEmb_jq ℚbar N) ω
  have hxθ : (x : LaurentSeries ℚbar) * thetaR (jqModC ℚbar) =
      ofPowerSeries ℤ ℚbar (PowerSeries.mk fun n => (a n : ℚbar)) := by
    rw [← hq, hx, diffQExpBar, diffQExp_smul_D, ← thetaL_eq_qEuler, thetaL_eq_thetaR, coe_J]

  obtain ⟨z, hz⟩ := exists_coeffMap_int_eq (x : LaurentSeries ℚbar) a hxθ
  obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq_of_int A z
  rw [hz] at hy
  refine ⟨y, hy ▸ x.2, ?_, by rw [hy]; exact hxθ⟩
  have hxy : (⟨coeffMap A.subtype y, hy ▸ x.2⟩ : modularFunctionFieldBar N) = x := Subtype.ext hy
  rw [hxy, ← hx]
  exact hreg

end Bar

section Main

local notation "ℚbar" => AlgebraicClosure ℚ

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N]

theorem qE_smul_D (K : Type*) [Field K] (g h : modularFunctionFieldC K N) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val (g • D K (modularFunctionFieldC K N) h) =
      (g : LaurentSeries K) * thetaL K (h : LaurentSeries K) := by
  have h1 := qExpansionDiffAlong_smul (modularFunctionFieldC K N).val g
    (D K (modularFunctionFieldC K N) h)
  have h2 := qExpansionDiffAlong_D (modularFunctionFieldC K N).val h
  exact h1.trans (congrArg (fun t => ((modularFunctionFieldC K N).val g) * t) h2)

theorem main (hpN : ¬ p ∣ N) (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ ω ∈ regularDifferentials (ResidueField A) (modularFunctionFieldC (ResidueField A) N),
      qExpansionDiffAlong (modularFunctionFieldC (ResidueField A) N).val ω =
        ofPowerSeries ℤ (ResidueField A) (PowerSeries.mk fun n => (a n : ResidueField A)) := by
  haveI : IsAlgClosed (ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (ResidueField A) p :=
    ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA

  obtain ⟨y, hy, hreg, hyθ⟩ := exists_integral_coefficient N A f a ha

  obtain ⟨R, r, hdict, -⟩ :=
    exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd N p hpN A hA
  obtain ⟨hint, hres⟩ := hdict y hy
  have hmemFull : coeffMap (residue A) y ∈ modularFunctionFieldFullC (ResidueField A) N := by
    rw [← hres]; exact SetLike.coe_mem _
  have hmem : coeffMap (residue A) y ∈ modularFunctionFieldC (ResidueField A) N := by
    rw [modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) p N hpN]
    exact hmemFull

  refine ⟨_, smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
    p N hpN A hA y hy hreg hmem, ?_⟩

  rw [qE_smul_D]
  change coeffMap (residue A) y * thetaL (ResidueField A) (jqModC (ResidueField A)) = _
  have hjA : jqModC (ResidueField A) = coeffMap (residue A) (jqModC A) := (map_jqModC _).symm
  rw [thetaL_eq_thetaR, hjA, ← coeffMap_thetaR, ← map_mul]
  have hyθA : y * thetaR (jqModC A) = ofPowerSeries ℤ A (PowerSeries.mk fun n => (a n : A)) := by
    apply coeffMap_injective A.subtype Subtype.val_injective
    rw [map_mul, coeffMap_thetaR, show coeffMap A.subtype (jqModC A) = jqModC ℚbar from
      map_jqModC _, hyθ, coeffMap_ofPowerSeries_intCast]
  rw [hyθA, coeffMap_ofPowerSeries_intCast]

end Main

end ModularCurve.Omega2ResidueProof
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve.Omega2ResidueProof"
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve"

p2m_open "ModularCurve~coeffEmb_jq~coeffMap_injective" in open _root_.P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast.ModularCurve AlgebraicCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ ω ∈ regularDifferentials (IsLocalRing.ResidueField A)
        (modularFunctionFieldC (IsLocalRing.ResidueField A) N),
      qExpansionDiffAlong (modularFunctionFieldC (IsLocalRing.ResidueField A) N).val ω =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A)
          (PowerSeries.mk fun n => (a n : IsLocalRing.ResidueField A)) :=
  ModularCurve.Omega2ResidueProof.main p N hpN A hA f a ha

end
end S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast
end P2MW
export P2MW.S_ModularCurve_exists_mem_regularDifferentials_residueField_qExpansionDiffAlong_eq_of_forall_qCoeff_eq_intCast (solution)
