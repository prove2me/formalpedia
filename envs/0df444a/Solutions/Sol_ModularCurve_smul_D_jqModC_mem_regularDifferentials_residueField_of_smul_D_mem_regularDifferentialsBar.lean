-- Prove2me | solution 1 for ModularCurve.smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4588a3dd-a394-5681-8c5a-35fb5277cf8c

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar
import Theorems.Thm_ModularCurve_exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_forall_valuationSubring_mem
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_Place_ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
import Theorems.Thm_ModularCurve_smul_D_jqModC_ne_zero
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_RegularProlongation_residue_integralClosure_surjective_of_genusFF_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval
import Theorems.Thm_AlgebraicCurve_exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_residue_trace_eq_trace_residue_of_finrank_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
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

p2m_open "ModularCurve~coeffEmb_jq~dedekindPsi_pos P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar.ModularCurve AlgebraicCurve KaehlerDifferential HahnSeries IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqModC_rat map_jqModC modularFunctionFieldC jqModC_mem jq dedekindPsi coeffMap coeffEmb coeffEmb_mem_laurentBaseChange jq_mem_full modularFunctionFieldBar regularDifferentialsBar modularFunctionFieldFullC jqModC_mem_full isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd modularFunctionFieldC_eq_modularFunctionFieldFullC laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi smul_D_jqModC_ne_zero transcendental_jqModC isCurveOver_modularFunctionFieldC_of_perfectField isCurveOver_laurentBaseChange_modularFunctionFieldFull isCurveOver_modularFunctionFieldFullC genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar"
namespace OmegaDReductionProof
p2m_open "ModularCurve~coeffEmb_jq~dedekindPsi_pos"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_coe_nonneg (v : Place K F) (f : v.toValuationSubring) : 0 ≤ v.ord (f : F) := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  have : (f : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ord_coe_nonneg v ⟨f, hf⟩

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem le_ord_add (v : Place K F) {a b : F} {m : ℤ} (ha : a = 0 ∨ m ≤ v.ord a)
    (hb : b = 0 ∨ m ≤ v.ord b) (hab : a + b ≠ 0) : m ≤ v.ord (a + b) := by
  rcases ha with rfl | ha
  · rw [zero_add] at hab ⊢
    exact hb.resolve_left hab
  rcases hb with rfl | hb
  · rw [add_zero]
    exact ha
  by_cases ha0 : a = 0
  · rw [ha0, zero_add] at hab ⊢; exact hb
  by_cases hb0 : b = 0
  · rw [hb0, add_zero]; exact ha
  exact (le_min ha hb).trans (Place.min_ord_le_ord_add v ha0 hb0 hab)

theorem ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, v.ord_zero]
  · exact ConstantReduction.ord_algebraMap v hc

theorem ord_neg (v : Place K F) (a : F) : v.ord (-a) = v.ord a := by
  by_cases ha : a = 0
  · rw [ha, neg_zero]
  rw [neg_eq_neg_one_mul, v.ord_mul (by norm_num) ha,
    show (-1 : F) = algebraMap K F (-1) by simp, ord_algebraMap', zero_add]

theorem exists_eq_mul_of_ord_pos (v : Place K F) {π : F} (hπ : v.ord π = 1) {a : F}
    (ha : 1 ≤ v.ord a) : ∃ b ∈ v.toValuationSubring, a = π * b := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  refine ⟨π⁻¹ * a, mem_of_ord_nonneg v ?_, by rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul]⟩
  by_cases ha0 : a = 0
  · rw [ha0, mul_zero, v.ord_zero]
  rw [v.ord_mul (inv_ne_zero hπ0) ha0, v.ord_inv, hπ]
  omega

end PlaceFacts

section LocalCalculus

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
variable (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (w : Place K F)

omit [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] in

theorem exists_uniformizer_dCoord : ∃ π : F, w.ord π = 1 ∧ w.dCoord = D K F π :=
  w.exists_ord_eq_one_and_dCoord_eq

variable {w}
variable {π : F} (hπ : w.ord π = 1) (hdc : w.dCoord = D K F π)

include hdc in
theorem D_eq_diffCoeff_smul (f : F) :
    D K F f = Place.diffCoeff π (D K F f) • D K F π := by
  haveI : w.DCoordGenerates := dCoordGenerates_of_isCurveOver w
  obtain ⟨c, hc⟩ := w.exists_eq_smul_dCoord (D K F f)
  rw [hdc] at hc
  exact (Place.diffCoeff_smul_D ⟨c, hc⟩).symm

include hdc in
theorem D_pi_ne_zero : D K F π ≠ 0 := by
  haveI : w.DCoordGenerates := dCoordGenerates_of_isCurveOver w
  rw [← hdc]; exact w.dCoord_ne_zero

include hdc in
theorem coeff_unique {a b : F} (h : a • D K F π = b • D K F π) : a = b :=
  smul_left_injective F (D_pi_ne_zero hdc) h

include hdc in
theorem diffCoeff_eq_of_eq {f c : F} (h : D K F f = c • D K F π) :
    Place.diffCoeff π (D K F f) = c :=
  coeff_unique hdc ((D_eq_diffCoeff_smul hdc f).symm.trans h)

include hdc in
theorem diffCoeff_pi : Place.diffCoeff π (D K F π) = 1 :=
  diffCoeff_eq_of_eq hdc (one_smul F _).symm

include hdc in

theorem diffCoeff_mul (f g : F) :
    Place.diffCoeff π (D K F (f * g)) =
      f * Place.diffCoeff π (D K F g) + g * Place.diffCoeff π (D K F f) := by
  apply diffCoeff_eq_of_eq hdc
  rw [Derivation.leibniz]
  conv_lhs => rw [D_eq_diffCoeff_smul hdc f, D_eq_diffCoeff_smul hdc g, smul_smul, smul_smul]
  rw [add_smul]

include hdc in
theorem diffCoeff_sub_algebraMap (f : F) (c : K) :
    Place.diffCoeff π (D K F (f - algebraMap K F c)) = Place.diffCoeff π (D K F f) := by
  apply diffCoeff_eq_of_eq hdc
  rw [map_sub, Derivation.map_algebraMap, sub_zero, ← D_eq_diffCoeff_smul hdc f]

include hdc in
theorem diffCoeff_inv (f : F) :
    Place.diffCoeff π (D K F f⁻¹) = -f⁻¹ ^ 2 * Place.diffCoeff π (D K F f) := by
  apply diffCoeff_eq_of_eq hdc
  rw [Derivation.leibniz_inv]
  conv_lhs => rw [D_eq_diffCoeff_smul hdc f, smul_smul]

include hdc in
theorem diffCoeff_pow (f : F) (n : ℕ) :
    Place.diffCoeff π (D K F (f ^ n)) = n * f ^ (n - 1) * Place.diffCoeff π (D K F f) := by
  apply diffCoeff_eq_of_eq hdc
  rw [Derivation.leibniz_pow]
  conv_lhs => rw [D_eq_diffCoeff_smul hdc f, smul_smul, ← Nat.cast_smul_eq_nsmul F, smul_smul,
    ← mul_assoc]

include x₀ hπ in
omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in

theorem ord_diffCoeff_nonneg {f : F} (hf : 0 ≤ w.ord f) :
    0 ≤ w.ord (Place.diffCoeff π (D K F f)) :=
  Place.ord_diffCoeff_D_nonneg_of_perfectField x₀ w hπ hf

include x₀ hπ hdc in

theorem ord_sub_one_le_ord_diffCoeff_of_pos {f : F} (hf : 1 ≤ w.ord f)
    (hD : Place.diffCoeff π (D K F f) ≠ 0) :
    w.ord f - 1 ≤ w.ord (Place.diffCoeff π (D K F f)) := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf

  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ w.ord f by omega)
  set u : F := f * (π ^ e)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (pow_ne_zero _ hπ0))
  have hordu : w.ord u = 0 := by
    rw [hu, w.ord_mul hf0 (inv_ne_zero (pow_ne_zero _ hπ0)), w.ord_inv, ← zpow_natCast,
      w.ord_zpow, hπ, he]; ring
  have hfu : f = π ^ e * u := by
    rw [hu, mul_comm, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπ0), mul_one]
  have hδu : 0 ≤ w.ord (Place.diffCoeff π (D K F u)) :=
    ord_diffCoeff_nonneg x₀ hπ (by rw [hordu])

  have he1 : 1 ≤ e := by
    have : (1 : ℤ) ≤ (e : ℤ) := by rw [← he]; exact hf
    exact_mod_cast this
  have hcalc : Place.diffCoeff π (D K F f) =
      π ^ (e - 1) * (π * Place.diffCoeff π (D K F u) + (e : F) * u) := by
    rw [hfu, diffCoeff_mul hdc, diffCoeff_pow hdc, diffCoeff_pi hdc, mul_one]
    have : π ^ e = π ^ (e - 1) * π := by
      rw [← pow_succ, Nat.sub_add_cancel he1]
    rw [this]; ring
  rw [hcalc] at hD ⊢
  have hin0 : π * Place.diffCoeff π (D K F u) + (e : F) * u ≠ 0 := fun h => by
    rw [h, mul_zero] at hD; exact hD rfl
  rw [w.ord_mul (pow_ne_zero _ hπ0) hin0, ← zpow_natCast, w.ord_zpow, hπ, mul_one, he]
  have hsum : 0 ≤ w.ord (π * Place.diffCoeff π (D K F u) + (e : F) * u) := by
    refine le_ord_add w ?_ ?_ hin0
    · by_cases h0 : Place.diffCoeff π (D K F u) = 0
      · left; rw [h0, mul_zero]
      · right; rw [w.ord_mul hπ0 h0, hπ]; omega
    · by_cases he0 : (e : F) = 0
      · left; rw [he0, zero_mul]
      · right
        rw [w.ord_mul he0 hu0, hordu, add_zero,
          show (e : F) = algebraMap K F (e : K) by simp, ord_algebraMap']
  push_cast [Nat.cast_sub he1]
  omega

include x₀ hπ hdc in

theorem neg_ord_sub_one_le_ord_diffCoeff_of_neg {j : F} (hj : w.ord j ≤ -1)
    (hD : Place.diffCoeff π (D K F j) ≠ 0) :
    w.ord j - 1 ≤ w.ord (Place.diffCoeff π (D K F j)) := by
  have hj0 : j ≠ 0 := by rintro rfl; simp at hj
  set s : F := j⁻¹ with hs
  have hs1 : 1 ≤ w.ord s := by rw [hs, w.ord_inv]; omega
  have hjs : j = s⁻¹ := by rw [hs, inv_inv]
  have hDs : Place.diffCoeff π (D K F s) ≠ 0 := by
    intro h0
    apply hD
    rw [hjs, diffCoeff_inv hdc, h0, mul_zero]
  have hbound := ord_sub_one_le_ord_diffCoeff_of_pos x₀ hπ hdc hs1 hDs
  have hords : w.ord s = - w.ord j := by rw [hs, w.ord_inv]
  rw [hjs, diffCoeff_inv hdc, w.ord_mul (by simp [hs, hj0]) hDs,
    show -s⁻¹ ^ 2 = -(s⁻¹ ^ 2) from rfl, ord_neg,
    ← zpow_natCast, w.ord_zpow, w.ord_inv, w.ord_inv]
  rw [hords] at hbound
  push_cast
  omega

include hdc in

theorem exists_mem_smul_D_eq_smul_dCoord {z f : F}
    (h : z * Place.diffCoeff π (D K F f) = 0 ∨
      0 ≤ w.ord (z * Place.diffCoeff π (D K F f))) :
    ∃ g ∈ w.toValuationSubring, z • D K F f = g • w.dCoord := by
  refine ⟨z * Place.diffCoeff π (D K F f), ?_, ?_⟩
  · rcases h with h | h
    · rw [h]; exact zero_mem _
    · exact mem_of_ord_nonneg w h
  · conv_lhs => rw [D_eq_diffCoeff_smul hdc f, smul_smul]
    rw [hdc]

include x₀ hπ hdc in

theorem ord_diffCoeff_eq_zero_of_ord_eq_one {t : F} (ht : w.ord t = 1) :
    w.ord (Place.diffCoeff π (D K F t)) = 0 ∧ Place.diffCoeff π (D K F t) ≠ 0 := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  set u : F := t * π⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero ht0 (inv_ne_zero hπ0)
  have hordu : w.ord u = 0 := by rw [hu, w.ord_mul ht0 (inv_ne_zero hπ0), w.ord_inv, hπ, ht]; ring
  have htu : t = π * u := by rw [hu, mul_comm, mul_assoc, inv_mul_cancel₀ hπ0, mul_one]
  have hδu : 0 ≤ w.ord (Place.diffCoeff π (D K F u)) :=
    ord_diffCoeff_nonneg x₀ hπ (by rw [hordu])
  have hcalc : Place.diffCoeff π (D K F t) = π * Place.diffCoeff π (D K F u) + u := by
    rw [htu, diffCoeff_mul hdc, diffCoeff_pi hdc, mul_one]

  have key : ¬ (1 ≤ w.ord (Place.diffCoeff π (D K F t))) ∧ Place.diffCoeff π (D K F t) ≠ 0 := by
    have hπδ : π * Place.diffCoeff π (D K F u) = 0 ∨ 1 ≤ w.ord (π * Place.diffCoeff π (D K F u)) := by
      by_cases h0 : Place.diffCoeff π (D K F u) = 0
      · left; rw [h0, mul_zero]
      · right; rw [w.ord_mul hπ0 h0, hπ]; omega
    constructor
    · intro h1
      have hu' : u = Place.diffCoeff π (D K F t) + -(π * Place.diffCoeff π (D K F u)) := by
        rw [hcalc]; ring
      have : 1 ≤ w.ord u := by
        rw [hu']
        refine le_ord_add w (Or.inr h1) ?_ (by rw [← hu']; exact hu0)
        rcases hπδ with h | h
        · left; rw [h, neg_zero]
        · right
          rwa [ord_neg]
      omega
    · intro h0
      rw [hcalc] at h0
      have hu' : u = -(π * Place.diffCoeff π (D K F u)) := eq_neg_of_add_eq_zero_right h0
      rcases hπδ with h | h
      · exact hu0 (by rw [hu', h, neg_zero])
      · have : 1 ≤ w.ord u := by
          rw [hu', ord_neg]
          exact h
        omega
  refine ⟨le_antisymm (by omega) ?_, key.2⟩
  have hmem : Place.diffCoeff π (D K F t) ∈ w.toValuationSubring := by
    rw [hcalc]
    exact add_mem (mul_mem (mem_of_ord_nonneg w (by rw [hπ]; omega)) (mem_of_ord_nonneg w hδu))
      (mem_of_ord_nonneg w (by rw [hordu]))
  exact ord_nonneg_of_mem w hmem

include x₀ hπ hdc in

theorem ordDiff_smul_D_eq {z f : F} (hz : z ≠ 0) (hD : Place.diffCoeff π (D K F f) ≠ 0) :
    w.ordDiff (z • D K F f) = w.ord z + w.ord (Place.diffCoeff π (D K F f)) := by
  have hex : ∃ t : F, w.ord t = 1 := ⟨π, hπ⟩
  have ht : w.ord w.uniformizer_alt = 1 := w.ord_uniformizer_alt hex
  set t := w.uniformizer_alt with htdef
  obtain ⟨hordt, hδt⟩ := ord_diffCoeff_eq_zero_of_ord_eq_one x₀ hπ hdc ht

  set g : F := z * Place.diffCoeff π (D K F f) * (Place.diffCoeff π (D K F t))⁻¹ with hg
  have hDt : D K F t = Place.diffCoeff π (D K F t) • D K F π := D_eq_diffCoeff_smul hdc t
  have hrep : z • D K F f = g • D K F t := by
    rw [hDt, smul_smul, hg, mul_assoc, inv_mul_cancel₀ hδt, mul_one]
    conv_lhs => rw [D_eq_diffCoeff_smul hdc f, smul_smul]
  have hDt0 : D K F t ≠ 0 := by
    rw [hDt]; exact smul_ne_zero hδt (D_pi_ne_zero hdc)
  have hcoeff : Place.diffCoeff t (z • D K F f) = g := by
    have h1 := Place.diffCoeff_smul_D (K := K) (t := t) (ω := z • D K F f) ⟨g, hrep⟩
    rw [hrep] at h1 ⊢
    exact smul_left_injective F hDt0 h1
  rw [Place.ordDiff_def, ← htdef, hcoeff, hg, w.ord_mul (mul_ne_zero hz hD) (inv_ne_zero hδt),
    w.ord_mul hz hD, w.ord_inv, hordt]
  ring

end LocalCalculus

section Helpers

theorem adjoin_simple_inv_eq {K E : Type*} [Field K] [Field E] [Algebra K E] (a : E) :
    IntermediateField.adjoin K ({a⁻¹} : Set E) = IntermediateField.adjoin K {a} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K a)
  · rw [IntermediateField.adjoin_simple_le_iff]
    rw [← inv_inv a, inv_inv a⁻¹]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K a⁻¹)

theorem transcendental_inv {R K : Type*} [CommRing R] [Field K] [Algebra R K] {x : K}
    (hx : Transcendental R x) : Transcendental R x⁻¹ := fun h =>
  hx (IsAlgebraic.inv_iff.mp h)

variable {F : Type*} [Field F]

theorem mem_of_monic_of_coeff_mem (V : ValuationSubring F) (Q : Polynomial F) (hQ : Q.Monic)
    (hc : ∀ i, Q.coeff i ∈ V) (g : F) (hg : Q.eval g = 0) : g ∈ V := by
  have hlift : Q ∈ Polynomial.lifts (algebraMap V F) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨Q.coeff n, hc n⟩, rfl⟩
  obtain ⟨Q', hQ'map, -, hQ'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQ
  have hint : IsIntegral V g := ⟨Q', hQ'monic, by rw [← Polynomial.eval_map, hQ'map, hg]⟩
  have hI : V.valuation.Integers V :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => V.valuation_le_one x
      exists_of_le_one := fun r hr => ⟨⟨r, (V.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have := hI.mem_of_integral hint
  exact (V.valuation_le_one_iff g).mp this

variable {L : Type*} [Field L] [Algebra L F]

theorem mem_of_isIntegral_adjoin_of_mem (x f : F)
    (hf : IsIntegral (Algebra.adjoin L ({x} : Set F)) f)
    (V : ValuationSubring F) (hVL : ∀ a : L, algebraMap L F a ∈ V) (hxV : x ∈ V) : f ∈ V := by
  obtain ⟨q, hqm, hq0⟩ := hf
  have hSV : Algebra.adjoin L ({x} : Set F) ≤ ⟨V.toSubring.toSubsemiring, hVL⟩ :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxV)
  refine mem_of_monic_of_coeff_mem V (q.map (algebraMap _ F)) (hqm.map _) (fun i => ?_) f ?_
  · rw [Polynomial.coeff_map]; exact hSV (q.coeff i).2
  · rwa [Polynomial.eval_map]

theorem aeval_mul_inv_pow_mem (V : ValuationSubring F) (hVL : ∀ a : L, algebraMap L F a ∈ V)
    {x : F} (hxinv : x⁻¹ ∈ V) (hx0 : x ≠ 0) (C : Polynomial L) {M : ℕ} (hM : C.natDegree ≤ M) :
    Polynomial.aeval x C * (x⁻¹) ^ M ∈ V := by
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine sum_mem fun i hi => ?_
  have hi' : i ≤ M := by have := Finset.mem_range.mp hi; omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi'
  have : C.coeff i • x ^ i * x⁻¹ ^ (i + d) = algebraMap L F (C.coeff i) * x⁻¹ ^ d := by
    rw [Algebra.smul_def, mul_assoc, _root_.pow_add, ← mul_assoc (x ^ i), ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow, one_mul]
  rw [this]
  exact mul_mem (hVL _) (pow_mem hxinv _)

theorem exists_forall_mul_inv_pow_mem (x f : F)
    (hf : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) :
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V := by
  obtain ⟨q, hqm, hq0⟩ := hf
  have hrep : ∀ i, ∃ C : Polynomial L,
      Polynomial.aeval x C = ((q.coeff i : Algebra.adjoin L ({x} : Set F)) : F) := fun i => by
    have hmem : ((q.coeff i : Algebra.adjoin L ({x} : Set F)) : F) ∈
        (Polynomial.aeval x : Polynomial L →ₐ[L] F).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (q.coeff i).2
    obtain ⟨C, hC⟩ := hmem
    exact ⟨C, hC⟩
  choose C hC using hrep
  refine ⟨(Finset.range (q.natDegree + 1)).sup fun i => (C i).natDegree, fun V hVL hxV => ?_⟩
  set n := q.natDegree with hn
  set m := (Finset.range (n + 1)).sup fun i => (C i).natDegree with hm
  have hx0 : x ≠ 0 := by rintro rfl; exact hxV (zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  set q₁ := q.map (algebraMap (Algebra.adjoin L ({x} : Set F)) F) with hq₁
  have hq₁m : q₁.Monic := hqm.map _
  have hq₁n : q₁.natDegree = n := hqm.natDegree_map _
  have hroot : Polynomial.eval ((x⁻¹) ^ m * f) (q₁.scaleRoots ((x⁻¹) ^ m)) = 0 := by
    have h0 : Polynomial.eval₂ (RingHom.id F) f q₁ = 0 := by
      rw [hq₁, Polynomial.eval₂_map]; simpa using hq0
    simpa using Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id F) (s := (x⁻¹) ^ m) h0
  have key : (x⁻¹) ^ m * f ∈ V := by
    refine mem_of_monic_of_coeff_mem V _ ((Polynomial.monic_scaleRoots_iff _).mpr hq₁m)
      (fun i => ?_) _ hroot
    rw [Polynomial.coeff_scaleRoots, hq₁n]
    by_cases hi : i < n
    · rw [hq₁, Polynomial.coeff_map, ← pow_mul]
      change ((q.coeff i : Algebra.adjoin L ({x} : Set F)) : F) * _ ∈ V
      rw [← hC i]
      have hdeg : (C i).natDegree ≤ m * (n - i) := by
        calc (C i).natDegree ≤ m :=
              Finset.le_sup (f := fun i => (C i).natDegree) (Finset.mem_range.mpr (by omega))
          _ ≤ m * (n - i) := Nat.le_mul_of_pos_right m (by omega)
      exact aeval_mul_inv_pow_mem V hVL hxinv hx0 (C i) hdeg
    · have hni : n - i = 0 := by omega
      rw [hni, pow_zero, mul_one]
      rcases (Nat.le_of_not_lt hi).lt_or_eq with h | h
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact zero_mem V
      · rw [← h, ← hq₁n, hq₁m.coeff_natDegree]; exact one_mem V
  rw [← inv_pow, mul_comm]
  exact key

end Helpers

section Reduction

local notation "ℚbar" => AlgebraicClosure ℚ

scoped instance isAlgebraic_rat_bar : Algebra.IsAlgebraic ℚ ℚbar := AlgebraicClosure.isAlgebraic ℚ

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ L)

variable (N : ℕ) [NeZero N]

def J : modularFunctionFieldBar N :=
  ⟨coeffEmb ℚbar jq, coeffEmb_mem_laurentBaseChange ℚbar (jq_mem_full N)⟩

theorem coe_J : ((J N : modularFunctionFieldBar N) : LaurentSeries ℚbar) = jqModC ℚbar :=
  coeffEmb_jq ℚbar

theorem J_ne_zero : (J N : modularFunctionFieldBar N) ≠ 0 := by
  intro h
  have := congrArg (fun z : modularFunctionFieldBar N => (z : LaurentSeries ℚbar)) h
  simp only [coe_J, ZeroMemClass.coe_zero] at this
  exact (transcendental_jqModC ℚbar) (this ▸ isAlgebraic_zero)

theorem dedekindPsi_pos : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
    rw [Finset.mem_filter]
    exact ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  calc 0 < N / 1 := by rw [Nat.div_one]; exact Nat.pos_of_ne_zero (NeZero.ne N)
    _ ≤ ∑ d ∈ N.divisors.filter Squarefree, N / d :=
        Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1

theorem finrank_adjoin_transport {K : Type*} [Field K]
    {E₁ E₂ : IntermediateField K (LaurentSeries K)} (h : E₁ = E₂) (z₁ z₂ : LaurentSeries K)
    (hz : z₁ = z₂) (hz₁ : z₁ ∈ E₁) (hz₂ : z₂ ∈ E₂) :
    Module.finrank (IntermediateField.adjoin K ({⟨z₁, hz₁⟩} : Set E₁)) E₁ =
      Module.finrank (IntermediateField.adjoin K ({⟨z₂, hz₂⟩} : Set E₂)) E₂ := by
  subst h; subst hz; rfl

theorem finrank_adjoin_J :
    Module.finrank (IntermediateField.adjoin ℚbar ({J N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) = dedekindPsi N := by
  have hE : modularFunctionFieldBar N = modularFunctionFieldFullC ℚbar N :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℚbar N
  have hN : (N : ℚbar) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [J, finrank_adjoin_transport hE (coeffEmb ℚbar jq) (jqModC ℚbar) (coeffEmb_jq ℚbar) _
    (jqModC_mem_full ℚbar N)]
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi ℚbar N hN

theorem finrank_adjoin_full (κ : Type*) [Field κ] (hN : (N : κ) ≠ 0)
    (z : modularFunctionFieldFullC κ N) (hz : (z : LaurentSeries κ) = jqModC κ) :
    Module.finrank (IntermediateField.adjoin κ ({z} : Set (modularFunctionFieldFullC κ N)))
      (modularFunctionFieldFullC κ N) = dedekindPsi N := by
  obtain ⟨z, hzmem⟩ := z
  change z = jqModC κ at hz
  subst hz
  exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi κ N hN

variable (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
variable (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)

local notation "F" => modularFunctionFieldBar N
local notation "κ" => ResidueField A
local notation "Fb" => modularFunctionFieldFullC (ResidueField A) N

include hpN in
omit [NeZero N] [Fact p.Prime] in
theorem natCast_ne_zero_residueField [CharP κ p] : (N : κ) ≠ 0 := fun h =>
  hpN ((CharP.cast_eq_zero_iff κ p N).mp h)

set_option maxHeartbeats 3200000 in
include hpN hA in

theorem exists_prolongation [IsAlgClosed κ] [CharP κ p] :
    ∃ (R : RegularProlongation A F Fb) (hJ : (J N : F) ∈ R.integers),
      (∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : F) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : Fb) : LaurentSeries κ) = coeffMap (residue A) y) ∧
      R.residue ⟨J N, hJ⟩ = ⟨jqModC κ, jqModC_mem_full κ N⟩ ∧
      Transcendental κ (R.residue ⟨J N, hJ⟩) ∧
      0 < Module.finrank (IntermediateField.adjoin κ ({R.residue ⟨J N, hJ⟩} : Set Fb)) Fb ∧
      Module.finrank (IntermediateField.adjoin ℚbar ({(J N : F)} : Set F)) F =
        Module.finrank (IntermediateField.adjoin κ ({R.residue ⟨J N, hJ⟩} : Set Fb)) Fb := by
  have hNκ : (N : κ) ≠ 0 := natCast_ne_zero_residueField N p hpN A
  obtain ⟨R, -, hdict, -⟩ :=
    exists_regularProlongation_placeMap_modularFunctionFieldFullC_of_not_dvd N p hpN A hA
  have hJy : coeffMap A.subtype (jqModC A) ∈ F := by
    rw [show coeffMap A.subtype (jqModC A) = (J N : LaurentSeries ℚbar) from
      (map_jqModC A.subtype).trans (coe_J N).symm]
    exact (J N).2
  obtain ⟨hJint', hJres'⟩ := hdict (jqModC A) hJy
  have hJeq : (⟨coeffMap A.subtype (jqModC A), hJy⟩ : F) = J N :=
    Subtype.ext ((map_jqModC A.subtype).trans (coe_J N).symm)
  have hJint : (J N : F) ∈ R.integers := hJeq ▸ hJint'
  have hJres : ((R.residue ⟨J N, hJint⟩ : Fb) : LaurentSeries κ) = jqModC κ := by
    have : (⟨J N, hJint⟩ : R.integers) = ⟨_, hJint'⟩ := Subtype.ext hJeq.symm
    rw [this, hJres']
    exact map_jqModC _
  have hJresEq : R.residue ⟨J N, hJint⟩ = ⟨jqModC κ, jqModC_mem_full κ N⟩ := Subtype.ext hJres
  have hJtr : Transcendental κ (R.residue ⟨J N, hJint⟩) := by
    rw [hJresEq, ← transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective Fb (LaurentSeries κ))]
    exact transcendental_jqModC κ
  refine ⟨R, hJint, hdict, hJresEq, hJtr, ?_, ?_⟩
  · rw [finrank_adjoin_full N κ hNκ _ hJres]; exact dedekindPsi_pos N
  · rw [finrank_adjoin_full N κ hNκ _ hJres]
    exact finrank_adjoin_J N

set_option maxHeartbeats 6400000 in
include hpN hA in

theorem reduction_bounds (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : F) • D ℚbar F (J N)) ∈ regularDifferentialsBar N)
    (hxb : coeffMap (residue A) y ∈ Fb) :
    ∃ m₁ m₂ : ℕ, ∀ w : Place κ Fb,
      ((m₁ : ℤ) * min 0 (w.ord (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb)) ≤
        w.ord ((⟨coeffMap (residue A) y, hxb⟩ : Fb) ^ 6 *
          (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) ^ 4 *
          ((⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) - algebraMap κ Fb 1728) ^ 3)) ∧
      ((m₂ : ℤ) * min 0 (w.ord (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb)⁻¹) ≤
        w.ord ((⟨coeffMap (residue A) y, hxb⟩ : Fb) ^ (2 * dedekindPsi N) *
          (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) ^ (dedekindPsi N + 1) *
          ((⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) - algebraMap κ Fb 1728) ^ dedekindPsi N)) := by
  haveI : IsAlgClosed κ := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP κ p := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  obtain ⟨R, hJint, hdict, hJresEq, hJtr, hfin, hdeg⟩ := exists_prolongation N p hpN A hA

  set x : F := ⟨coeffMap A.subtype y, hy⟩ with hxdef
  obtain ⟨hxint, hxres⟩ := hdict y hy
  set Jr : R.integers := ⟨J N, hJint⟩ with hJrdef
  have hJres : ((R.residue Jr : Fb) : LaurentSeries κ) = jqModC κ := by rw [hJresEq]
  set Xr : R.integers := ⟨x, hxint⟩ with hXrdef
  have hXresEq : R.residue Xr = ⟨coeffMap (residue A) y, hxb⟩ := Subtype.ext hxres
  have hcint : algebraMap ℚbar F 1728 ∈ R.integers := by
    rw [show (1728 : ℚbar) = ((1728 : A) : ℚbar) by norm_cast, R.algebraMap_mem_iff]
    exact SetLike.coe_mem _
  set Cr : R.integers := ⟨algebraMap ℚbar F 1728, hcint⟩ with hCrdef
  have hCres : R.residue Cr = algebraMap κ Fb 1728 := by
    have h := R.residue_algebraMap (1728 : A)
    have hCr : Cr = ⟨algebraMap ℚbar F ((1728 : A) : ℚbar), (R.algebraMap_mem_iff _).mpr (1728 : A).2⟩ :=
      Subtype.ext (by rw [hCrdef]; norm_cast)
    rw [hCr, h, map_ofNat]
  have huniq : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin ℚbar {(Jr : F)} → (e ∈ V ↔ e ∈ R.integers)) →
      V = R.integers := fun V hV =>
    R.eq_integers_of_forall_mem_adjoin_iff A Jr hJtr hfin hdeg V hV

  obtain ⟨hint₁, hint₂⟩ := isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentialsBar N x hreg
  set u₁ : F := x ^ 6 * (J N) ^ 4 * (J N - algebraMap ℚbar F 1728) ^ 3 with hu₁
  set u₂ : F := x ^ (2 * dedekindPsi N) * (J N) ^ (dedekindPsi N + 1) *
    (J N - algebraMap ℚbar F 1728) ^ dedekindPsi N with hu₂
  change IsIntegral (Algebra.adjoin ℚbar ({(J N : F)} : Set F)) u₁ at hint₁
  change IsIntegral (Algebra.adjoin ℚbar ({(J N : F)⁻¹} : Set F)) u₂ at hint₂
  have hu₁O : u₁ ∈ R.integers := by
    have : u₁ = ((Xr ^ 6 * Jr ^ 4 * (Jr - Cr) ^ 3 : R.integers) : F) := by
      rw [hu₁]; rfl
    rw [this]; exact SetLike.coe_mem _
  have hu₂O : u₂ ∈ R.integers := by
    have : u₂ = ((Xr ^ (2 * dedekindPsi N) * Jr ^ (dedekindPsi N + 1) *
        (Jr - Cr) ^ dedekindPsi N : R.integers) : F) := by
      rw [hu₂]; rfl
    rw [this]; exact SetLike.coe_mem _
  have hres₁ : R.residue ⟨u₁, hu₁O⟩ =
      (⟨coeffMap (residue A) y, hxb⟩ : Fb) ^ 6 * (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) ^ 4 *
        ((⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) - algebraMap κ Fb 1728) ^ 3 := by
    have : (⟨u₁, hu₁O⟩ : R.integers) = Xr ^ 6 * Jr ^ 4 * (Jr - Cr) ^ 3 :=
      Subtype.ext (show u₁ = _ by rw [hu₁]; rfl)
    rw [this, map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hXresEq, hJresEq, hCres]
  have hres₂ : R.residue ⟨u₂, hu₂O⟩ =
      (⟨coeffMap (residue A) y, hxb⟩ : Fb) ^ (2 * dedekindPsi N) *
        (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) ^ (dedekindPsi N + 1) *
        ((⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) - algebraMap κ Fb 1728) ^ dedekindPsi N := by
    have : (⟨u₂, hu₂O⟩ : R.integers) =
        Xr ^ (2 * dedekindPsi N) * Jr ^ (dedekindPsi N + 1) * (Jr - Cr) ^ dedekindPsi N :=
      Subtype.ext (show u₂ = _ by rw [hu₂]; rfl)
    rw [this, map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hXresEq, hJresEq, hCres]

  have hJinvO : (J N : F)⁻¹ ∈ R.integers := by
    have hu : IsUnit Jr := R.isUnit_of_residue_ne_zero (fun h => by
      have := congrArg (fun z : Fb => (z : LaurentSeries κ)) h
      simp only [hJres, ZeroMemClass.coe_zero] at this
      exact (transcendental_jqModC κ) (this ▸ isAlgebraic_zero))
    rw [← R.integers.valuation_le_one_iff, map_inv₀,
      ((R.integers.valuation_eq_one_iff Jr).mp hu), inv_one]
  set Jinv : R.integers := ⟨(J N : F)⁻¹, hJinvO⟩ with hJinvdef
  have hJinvres : R.residue Jinv = (R.residue Jr)⁻¹ := by
    have h1 : Jinv * Jr = 1 := Subtype.ext (inv_mul_cancel₀ (J_ne_zero N))
    have h2 : R.residue Jinv * R.residue Jr = 1 := by rw [← map_mul, h1, map_one]
    exact eq_inv_of_mul_eq_one_left h2
  have hJinvtr : Transcendental κ (R.residue Jinv) := by
    rw [hJinvres]; exact transcendental_inv hJtr

  obtain ⟨m₁, hm₁⟩ := exists_forall_mul_inv_pow_mem (L := ℚbar) (J N : F) u₁ hint₁
  obtain ⟨m₂, hm₂⟩ := exists_forall_mul_inv_pow_mem (L := ℚbar) (J N : F)⁻¹ u₂ hint₂
  refine ⟨m₁, m₂, fun w => ⟨?_, ?_⟩⟩
  · have h := R.mul_min_ord_residue_le_of_forall_valuationSubring_mem A Jr hJtr u₁ m₁
      (fun V hVL hxV => mem_of_isIntegral_adjoin_of_mem (L := ℚbar) (J N : F) u₁ hint₁ V hVL hxV)
      hm₁ (fun V hV => by rw [huniq V hV]; exact hu₁O) hu₁O w
    rwa [hJresEq, hres₁] at h
  · have h := R.mul_min_ord_residue_le_of_forall_valuationSubring_mem A Jinv hJinvtr u₂ m₂
      (fun V hVL hxV => mem_of_isIntegral_adjoin_of_mem (L := ℚbar) (J N : F)⁻¹ u₂ hint₂ V hVL hxV)
      hm₂ (fun V hV => by
        rw [huniq V (fun e he => hV e (by rwa [hJinvdef, adjoin_simple_inv_eq]))]
        exact hu₂O) hu₂O w
    rwa [hJinvres, hJresEq, hres₂] at h

end Reduction

section Rational

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [IsAlgClosed K] [IsCurveOver K E]

theorem exists_one_le_ord_sub_algebraMap (w : Place K E) {f : E} (hf : 0 ≤ w.ord f)
    (hfc : ∀ c : K, f - algebraMap K E c ≠ 0) :
    ∃ c : K, 1 ≤ w.ord (f - algebraMap K E c) := by
  haveI : Module.Finite K w.ResidueField := IsCurveOver.finiteResidue w
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  set fO : w.toValuationSubring := ⟨f, mem_of_ord_nonneg w hf⟩ with hfO
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := w.ResidueField)).2 (IsLocalRing.residue w.toValuationSubring fO)
  refine ⟨c, ?_⟩
  have hmem : fO - algebraMap K w.toValuationSubring c ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    rw [IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField c]
    exact sub_self _
  have hcoe : ((fO - algebraMap K w.toValuationSubring c : w.toValuationSubring) : E) =
      f - algebraMap K E c := by
    rw [hfO]; push_cast; rw [Place.coe_algebraMap]
  have hne : f - algebraMap K E c ≠ 0 := hfc c
  have h0 : 0 ≤ w.ord (f - algebraMap K E c) := by
    rw [← hcoe]; exact ord_coe_nonneg w _

  by_contra hlt
  have hz : w.ord (f - algebraMap K E c) = 0 := by omega
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hne hπ
  rw [hz, zpow_zero, mul_one] at hu
  have hunit : IsUnit (fO - algebraMap K w.toValuationSubring c) := by
    have : fO - algebraMap K w.toValuationSubring c = (u : w.toValuationSubring) :=
      Subtype.ext (hcoe.trans hu)
    rw [this]; exact Units.isUnit u
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit

end Rational

section CField

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

theorem finiteDimensional_adjoin_jqModC (hN : (N : K) ≠ 0) :
    FiniteDimensional
      (IntermediateField.adjoin K
        ({⟨jqModC K, jqModC_mem K N⟩} : Set (modularFunctionFieldC K N)))
      (modularFunctionFieldC K N) := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hℓN : ¬ ℓ ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K ℓ N).mpr h)
  have hE : modularFunctionFieldC K N = modularFunctionFieldFullC K N :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC K ℓ N hℓN
  suffices H : ∀ (E : IntermediateField K (LaurentSeries K)) (hj : jqModC K ∈ E),
      E = modularFunctionFieldFullC K N →
      FiniteDimensional (IntermediateField.adjoin K ({⟨jqModC K, hj⟩} : Set E)) E from
    H _ (jqModC_mem K N) hE
  rintro E hj rfl
  apply FiniteDimensional.of_finrank_pos
  rw [finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN]
  exact dedekindPsi_pos N

theorem transcendental_jqModC_mem :
    Transcendental K (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) := by
  have h := transcendental_jqModC K
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (modularFunctionFieldC K N) (LaurentSeries K))]
  exact h

theorem essFiniteType (hN : (N : K) ≠ 0) :
    Algebra.EssFiniteType K (modularFunctionFieldC K N) :=
  haveI := finiteDimensional_adjoin_jqModC K N hN
  essFiniteType_of_transcendental_of_finiteDimensional (transcendental_jqModC_mem K N) ‹_›

theorem jqModC_sub_algebraMap_ne_zero (c : K) :
    (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) -
      algebraMap K (modularFunctionFieldC K N) c ≠ 0 := by
  intro h
  have h' : (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) =
      algebraMap K (modularFunctionFieldC K N) c := sub_eq_zero.mp h
  exact transcendental_jqModC_mem K N (h' ▸ isAlgebraic_algebraMap c)

theorem jqModC_mem_ne_zero :
    (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) ≠ 0 := by
  have h := jqModC_sub_algebraMap_ne_zero K N 0
  rwa [map_zero, sub_zero] at h

end CField

section Transport

local notation "ℚbar" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
variable (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)

local notation "F" => modularFunctionFieldBar N
local notation "κ" => ResidueField A
local notation "F₁" => modularFunctionFieldC (ResidueField A) N

set_option maxHeartbeats 6400000 in
include hpN hA in

theorem reduction_bounds_C (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : F) • D ℚbar F (J N)) ∈ regularDifferentialsBar N)
    (hmem : coeffMap (residue A) y ∈ F₁) :
    ∃ m₁ m₂ : ℕ, ∀ w : Place κ F₁,
      ((m₁ : ℤ) * min 0 (w.ord (⟨jqModC κ, jqModC_mem κ N⟩ : F₁)) ≤
        w.ord ((⟨coeffMap (residue A) y, hmem⟩ : F₁) ^ 6 *
          (⟨jqModC κ, jqModC_mem κ N⟩ : F₁) ^ 4 *
          ((⟨jqModC κ, jqModC_mem κ N⟩ : F₁) - algebraMap κ F₁ 1728) ^ 3)) ∧
      ((m₂ : ℤ) * min 0 (w.ord (⟨jqModC κ, jqModC_mem κ N⟩ : F₁)⁻¹) ≤
        w.ord ((⟨coeffMap (residue A) y, hmem⟩ : F₁) ^ (2 * dedekindPsi N) *
          (⟨jqModC κ, jqModC_mem κ N⟩ : F₁) ^ (dedekindPsi N + 1) *
          ((⟨jqModC κ, jqModC_mem κ N⟩ : F₁) - algebraMap κ F₁ 1728) ^ dedekindPsi N)) := by
  haveI : CharP κ p := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  have hCF : modularFunctionFieldC κ N = modularFunctionFieldFullC κ N :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC κ p N hpN
  suffices H : ∀ (E : IntermediateField κ (LaurentSeries κ)) (hj : jqModC κ ∈ E)
      (hx : coeffMap (residue A) y ∈ E), E = modularFunctionFieldFullC κ N →
      ∃ m₁ m₂ : ℕ, ∀ w : Place κ E,
        ((m₁ : ℤ) * min 0 (w.ord (⟨jqModC κ, hj⟩ : E)) ≤
          w.ord ((⟨coeffMap (residue A) y, hx⟩ : E) ^ 6 * (⟨jqModC κ, hj⟩ : E) ^ 4 *
            ((⟨jqModC κ, hj⟩ : E) - algebraMap κ E 1728) ^ 3)) ∧
        ((m₂ : ℤ) * min 0 (w.ord (⟨jqModC κ, hj⟩ : E)⁻¹) ≤
          w.ord ((⟨coeffMap (residue A) y, hx⟩ : E) ^ (2 * dedekindPsi N) *
            (⟨jqModC κ, hj⟩ : E) ^ (dedekindPsi N + 1) *
            ((⟨jqModC κ, hj⟩ : E) - algebraMap κ E 1728) ^ dedekindPsi N)) from
    H _ (jqModC_mem κ N) hmem hCF
  rintro E hj hx rfl
  exact reduction_bounds N p hpN A hA y hy hreg hx

end Transport

section TraceRoute

local notation "ℚbar" => AlgebraicClosure ℚ

theorem isIntegral_adjoin_congr {K E : Type*} [Field K] [Field E] [Algebra K E] {a b : E}
    (h : a = b) {z : E} (hz : IsIntegral (Algebra.adjoin K ({a} : Set E)) z) :
    IsIntegral (Algebra.adjoin K ({b} : Set E)) z := by
  subst h; exact hz

theorem trace_adjoin_congr {K E : Type*} [Field K] [Field E] [Algebra K E] {a b : E}
    (h : a = b) (z : E) :
    ((Algebra.trace (IntermediateField.adjoin K ({a} : Set E)) E z :
        IntermediateField.adjoin K ({a} : Set E)) : E) =
      ((Algebra.trace (IntermediateField.adjoin K ({b} : Set E)) E z :
        IntermediateField.adjoin K ({b} : Set E)) : E) := by
  subst h; rfl

variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
variable (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)

local notation "F" => modularFunctionFieldBar N
local notation "κ" => ResidueField A
local notation "Fb" => modularFunctionFieldFullC (ResidueField A) N

def constToIntegers (R : RegularProlongation A F Fb) : A →+* R.integers where
  toFun a := ⟨algebraMap ℚbar F a, (R.algebraMap_mem_iff _).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

omit [NeZero N] in
theorem coe_constToIntegers (R : RegularProlongation A F Fb) (a : A) :
    ((constToIntegers N A R a : R.integers) : F) = algebraMap ℚbar F a := rfl

omit [NeZero N] in
theorem residue_constToIntegers (R : RegularProlongation A F Fb) (a : A) :
    R.residue (constToIntegers N A R a) = algebraMap κ Fb (residue A a) :=
  R.residue_algebraMap a

omit [NeZero N] in

theorem residue_eval₂_constToIntegers (R : RegularProlongation A F Fb) (P : Polynomial A)
    (Jr : R.integers) :
    ((P.eval₂ (constToIntegers N A R) Jr : R.integers) : F) =
        Polynomial.aeval (Jr : F) (P.map A.subtype) ∧
      R.residue (P.eval₂ (constToIntegers N A R) Jr) =
        Polynomial.aeval (R.residue Jr) (P.map (residue A)) := by
  constructor
  · rw [show ((P.eval₂ (constToIntegers N A R) Jr : R.integers) : F) =
        R.integers.subtype (P.eval₂ (constToIntegers N A R) Jr) from rfl,
      Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
  · rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext fun a => residue_constToIntegers N A R a

set_option maxHeartbeats 6400000 in
include hpN hA in

theorem finite_places (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : F) • D ℚbar F (J N)) ∈ regularDifferentialsBar N)
    (hxb : coeffMap (residue A) y ∈ Fb) (w : Place κ Fb)
    (hw : 0 ≤ w.ord (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb)) :
    ∃ g ∈ w.toValuationSubring,
      (⟨coeffMap (residue A) y, hxb⟩ : Fb) • D κ Fb (⟨jqModC κ, jqModC_mem_full κ N⟩ : Fb) =
        g • w.dCoord := by
  haveI : IsAlgClosed κ := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP κ p := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  have hNκ : (N : κ) ≠ 0 := natCast_ne_zero_residueField N p hpN A
  obtain ⟨R, hJint, hdict, hJresEq, hJtr, hfin, hdeg⟩ := exists_prolongation N p hpN A hA
  set x : F := ⟨coeffMap A.subtype y, hy⟩ with hxdef
  obtain ⟨hxint, hxres⟩ := hdict y hy
  set Jr : R.integers := ⟨J N, hJint⟩ with hJrdef
  set Xr : R.integers := ⟨x, hxint⟩ with hXrdef
  set jb : Fb := ⟨jqModC κ, jqModC_mem_full κ N⟩ with hjbdef
  set xb : Fb := ⟨coeffMap (residue A) y, hxb⟩ with hxbdef
  have hXresEq : R.residue Xr = xb := Subtype.ext hxres

  haveI : IsCurveOver ℚbar F := isCurveOver_laurentBaseChange_modularFunctionFieldFull ℚbar N
  haveI : IsCurveOver κ Fb := isCurveOver_modularFunctionFieldFullC κ N
  haveI hfdF : FiniteDimensional (IntermediateField.adjoin ℚbar ({(J N : F)} : Set F)) F := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_adjoin_J N]; exact dedekindPsi_pos N
  haveI hfdFb : FiniteDimensional (IntermediateField.adjoin κ ({jb} : Set Fb)) Fb := by
    apply FiniteDimensional.of_finrank_pos
    rw [finrank_adjoin_full N κ hNκ jb rfl]; exact dedekindPsi_pos N
  have hJtrL : Transcendental ℚbar (J N : F) := by
    rw [← transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective F (LaurentSeries ℚbar))]
    change Transcendental ℚbar ((J N : F) : LaurentSeries ℚbar)
    rw [coe_J]
    exact transcendental_jqModC ℚbar
  have hjbtr : Transcendental κ jb := by
    rw [← transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective Fb (LaurentSeries κ))]
    exact transcendental_jqModC κ

  have hgood : genusFF κ Fb = genusFF ℚbar F :=
    genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar κ N hNκ
  have hchart := (R.residue_integralClosure_surjective_of_genusFF_eq A Jr hJtr hfin hdeg hgood).1

  have hxreg : ∀ v : Place ℚbar F, 0 ≤ v.ord (J N : F) →
      ∃ g ∈ v.toValuationSubring, x • D ℚbar F (J N) = g • v.dCoord := fun v _ => hreg v

  have hdual : ∀ b : Fb, IsIntegral (Algebra.adjoin κ ({jb} : Set Fb)) b →
      ∃ P : Polynomial κ,
        ((Algebra.trace (IntermediateField.adjoin κ ({jb} : Set Fb)) Fb (xb * b) :
            IntermediateField.adjoin κ ({jb} : Set Fb)) : Fb) = Polynomial.aeval jb P := by
    intro b hb

    obtain ⟨B, hBint, hBres⟩ := hchart b (isIntegral_adjoin_congr hJresEq.symm hb)

    obtain ⟨P, hP⟩ :=
      exists_trace_mul_eq_aeval_of_forall_exists_smul_D_eq_smul_dCoord (J N : F) hJtrL x hxreg
        (B : F) hBint

    obtain ⟨hTint₀, hTres₀⟩ :=
      R.exists_residue_trace_eq_trace_residue_of_finrank_eq A Jr hJtr hfin hdeg (Xr * B)
    have hTint : ((Algebra.trace (IntermediateField.adjoin ℚbar ({(Jr : F)} : Set F)) F (x * B) :
        IntermediateField.adjoin ℚbar ({(Jr : F)} : Set F)) : F) ∈ R.integers := hTint₀
    have hTres : R.residue ⟨_, hTint⟩ =
        ((Algebra.trace (IntermediateField.adjoin κ ({R.residue Jr} : Set Fb)) Fb
            (R.residue (Xr * B)) : IntermediateField.adjoin κ ({R.residue Jr} : Set Fb)) : Fb) :=
      hTres₀

    have hPint : Polynomial.aeval (Jr : F) P ∈ R.integers := by
      change Polynomial.aeval (J N : F) P ∈ R.integers
      rw [← hP]; exact hTint
    have hcoeff : ∀ i, P.coeff i ∈ A := fun i =>
      R.coeff_mem_of_aeval_mem_integers A Jr hJtr P hPint i

    have hlift : P ∈ Polynomial.lifts (algebraMap A ℚbar) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun i => ⟨⟨P.coeff i, hcoeff i⟩, rfl⟩
    obtain ⟨PA, hPA⟩ := (Polynomial.mem_lifts _).mp hlift
    have hPA' : PA.map A.subtype = P := hPA
    obtain ⟨heval, hevalres⟩ := residue_eval₂_constToIntegers N A R PA Jr
    rw [hPA'] at heval
    refine ⟨PA.map (residue A), ?_⟩
    have h1 : (⟨_, hTint⟩ : R.integers) = PA.eval₂ (constToIntegers N A R) Jr :=
      Subtype.ext (by rw [heval, ← hP])
    have hprod : R.residue (Xr * B) = xb * b := by rw [map_mul, hXresEq, hBres]
    rw [← trace_adjoin_congr hJresEq (xb * b), ← hprod, ← hTres, h1, hevalres, hJresEq]

  exact exists_smul_D_eq_smul_dCoord_of_forall_isIntegral_trace_mul_eq_aeval jb hjbtr xb hdual w hw

set_option maxHeartbeats 6400000 in
include hpN hA in

theorem finite_places_C (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : F) • D ℚbar F (J N)) ∈ regularDifferentialsBar N)
    (hmem : coeffMap (residue A) y ∈ modularFunctionFieldC κ N)
    (w : Place κ (modularFunctionFieldC κ N))
    (hw : 0 ≤ w.ord (⟨jqModC κ, jqModC_mem κ N⟩ : modularFunctionFieldC κ N)) :
    ∃ g ∈ w.toValuationSubring,
      (⟨coeffMap (residue A) y, hmem⟩ : modularFunctionFieldC κ N) •
          D κ (modularFunctionFieldC κ N) (⟨jqModC κ, jqModC_mem κ N⟩ : modularFunctionFieldC κ N) =
        g • w.dCoord := by
  haveI : CharP κ p := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  have hCF : modularFunctionFieldC κ N = modularFunctionFieldFullC κ N :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC κ p N hpN
  suffices H : ∀ (E : IntermediateField κ (LaurentSeries κ)) (hj : jqModC κ ∈ E)
      (hx : coeffMap (residue A) y ∈ E), E = modularFunctionFieldFullC κ N →
      ∀ w : Place κ E, 0 ≤ w.ord (⟨jqModC κ, hj⟩ : E) →
        ∃ g ∈ w.toValuationSubring,
          (⟨coeffMap (residue A) y, hx⟩ : E) • D κ E (⟨jqModC κ, hj⟩ : E) = g • w.dCoord from
    H _ (jqModC_mem κ N) hmem hCF w hw
  rintro E hj hx rfl
  exact finite_places N p hpN A hA y hy hreg hx

end TraceRoute

section Main

local notation "ℚbar" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
variable (A : ValuationSubring ℚbar) (hA : A.LiesOverPrime p)

local notation "F" => modularFunctionFieldBar N
local notation "κ" => ResidueField A
local notation "F₁" => modularFunctionFieldC (ResidueField A) N

set_option maxHeartbeats 6400000 in
include hpN hA in

theorem main (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ F)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : F) • D ℚbar F (J N)) ∈ regularDifferentialsBar N)
    (hmem : coeffMap (residue A) y ∈ F₁)
    (hwild : (1728 : κ) = 0 → ∀ w : Place κ F₁,
      1 ≤ w.ord (⟨jqModC κ, jqModC_mem κ N⟩ : F₁) →
      ∃ g ∈ w.toValuationSubring,
        (⟨coeffMap (residue A) y, hmem⟩ : F₁) • D κ F₁ (⟨jqModC κ, jqModC_mem κ N⟩ : F₁) =
          g • w.dCoord) :
    ((⟨coeffMap (residue A) y, hmem⟩ : F₁) • D κ F₁ (⟨jqModC κ, jqModC_mem κ N⟩ : F₁)) ∈
      regularDifferentials κ F₁ := by
  haveI : IsAlgClosed κ := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP κ p := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  have hNκ : (N : κ) ≠ 0 := natCast_ne_zero_residueField N p hpN A
  haveI := finiteDimensional_adjoin_jqModC κ N hNκ
  haveI : Algebra.EssFiniteType κ F₁ := essFiniteType κ N hNκ
  haveI : IsCurveOver κ F₁ := isCurveOver_modularFunctionFieldC_of_perfectField κ N
  set xb : F₁ := ⟨coeffMap (residue A) y, hmem⟩ with hxb
  set jb : F₁ := ⟨jqModC κ, jqModC_mem κ N⟩ with hjb
  obtain ⟨m₁, m₂, hbounds⟩ := reduction_bounds_C N p hpN A hA y hy hreg hmem
  intro w

  by_cases hx0 : xb = 0
  · exact ⟨0, zero_mem _, by rw [hx0, zero_smul, zero_smul]⟩
  obtain ⟨π, hπ, hdc⟩ := exists_uniformizer_dCoord w
  have hDj : D κ F₁ jb ≠ 0 := by
    have h := smul_D_jqModC_ne_zero (K := κ) (ℓ := N) jb (z := (1 : F₁)) one_ne_zero
    rwa [one_smul] at h
  have hδj : Place.diffCoeff π (D κ F₁ jb) ≠ 0 := fun h =>
    hDj (by rw [D_eq_diffCoeff_smul hdc jb, h, zero_smul])
  have hjb0 : jb ≠ 0 := jqModC_mem_ne_zero κ N
  have hjc0 : jb - algebraMap κ F₁ 1728 ≠ 0 := jqModC_sub_algebraMap_ne_zero κ N 1728
  obtain ⟨hb₁, hb₂⟩ := hbounds w

  suffices key : (1728 : κ) = 0 ∧ 1 ≤ w.ord jb ∨
      0 ≤ w.ord xb + w.ord (Place.diffCoeff π (D κ F₁ jb)) by
    rcases key with ⟨h1728, hss⟩ | key
    · exact hwild h1728 w hss
    · exact exists_mem_smul_D_eq_smul_dCoord hdc (Or.inr (by rwa [w.ord_mul hx0 hδj]))
  rcases lt_or_ge (w.ord jb) 0 with hcusp | hfin
  ·
    right
    have hmin : min 0 (w.ord jb⁻¹) = 0 := by rw [w.ord_inv]; omega
    rw [hmin, mul_zero, w.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hjb0))
      (pow_ne_zero _ hjc0), w.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hjb0),
      ← zpow_natCast, w.ord_zpow, ← zpow_natCast, w.ord_zpow, ← zpow_natCast, w.ord_zpow] at hb₂
    have hjc : w.ord (jb - algebraMap κ F₁ 1728) ≤ w.ord jb := by
      by_cases hc : (1728 : κ) = 0
      · rw [hc, map_zero, sub_zero]
      have h := Place.min_ord_le_ord_add w hjc0 ((map_ne_zero _).mpr hc)
        (by rw [sub_add_cancel]; exact hjb0)
      rw [sub_add_cancel, ord_algebraMap'] at h
      omega
    have hψ : (1 : ℤ) ≤ dedekindPsi N := by exact_mod_cast dedekindPsi_pos N
    have hxlow : -w.ord jb + 1 ≤ w.ord xb := by
      by_contra hlt
      push Not at hlt
      push_cast at hb₂
      nlinarith
    have hpole := neg_ord_sub_one_le_ord_diffCoeff_of_neg jb hπ hdc (by omega) hδj
    omega
  · by_cases h1728 : (1728 : κ) = 0
    · rcases hfin.lt_or_eq with hss | hgen
      · exact Or.inl ⟨h1728, by omega⟩
      ·
        right
        have hmin : min 0 (w.ord jb) = 0 := by omega
        rw [hmin, mul_zero, h1728, map_zero, sub_zero,
          w.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hjb0)) (pow_ne_zero _ hjb0),
          w.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hjb0),
          ← zpow_natCast, w.ord_zpow, ← zpow_natCast, w.ord_zpow, ← zpow_natCast, w.ord_zpow,
          ← hgen] at hb₁
        have hx : 0 ≤ w.ord xb := by push_cast at hb₁; omega
        obtain ⟨c, hc⟩ := exists_one_le_ord_sub_algebraMap w hfin
          (jqModC_sub_algebraMap_ne_zero κ N)
        have hδ := ord_sub_one_le_ord_diffCoeff_of_pos jb hπ hdc hc
          (by rwa [diffCoeff_sub_algebraMap hdc])
        rw [diffCoeff_sub_algebraMap hdc] at hδ
        omega
    ·
      right
      have hmin : min 0 (w.ord jb) = 0 := by omega
      rw [hmin, mul_zero] at hb₁
      have h := Place.ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
        w jb xb jb h1728 hb₁
      rwa [ordDiff_smul_D_eq jb hπ hdc hx0 hδj] at h

include hpN hA in

theorem main_of_ne_zero (h1728 : (1728 : κ) ≠ 0) (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ F)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : F) • D ℚbar F (J N)) ∈ regularDifferentialsBar N)
    (hmem : coeffMap (residue A) y ∈ F₁) :
    ((⟨coeffMap (residue A) y, hmem⟩ : F₁) • D κ F₁ (⟨jqModC κ, jqModC_mem κ N⟩ : F₁)) ∈
      regularDifferentials κ F₁ :=
  main N p hpN A hA y hy hreg hmem (fun h => absurd h h1728)

end Main

end ModularCurve.OmegaDReductionProof
p2m_reactivate "P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar.ModularCurve P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar.ModularCurve.OmegaDReductionProof"
p2m_reactivate "P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar.ModularCurve"

p2m_open "ModularCurve~coeffEmb_jq~dedekindPsi_pos" in open _root_.P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar.ModularCurve AlgebraicCurve IsLocalRing in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (y : LaurentSeries A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N)
    (hreg : ((⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) •
        KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
              modularFunctionFieldBar N)) ∈ regularDifferentialsBar N)
    (hmem : coeffMap (residue A) y ∈ modularFunctionFieldC (ResidueField A) N) :
    ((⟨coeffMap (residue A) y, hmem⟩ : modularFunctionFieldC (ResidueField A) N) •
        KaehlerDifferential.D (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
            modularFunctionFieldC (ResidueField A) N)) ∈
      regularDifferentials (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
  ModularCurve.OmegaDReductionProof.main N p hpN A hA y hy hreg hmem
    (fun _ w hw => ModularCurve.OmegaDReductionProof.finite_places_C N p hpN A hA y hy hreg hmem w
      (le_trans zero_le_one hw))

end
end S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar
end P2MW
export P2MW.S_ModularCurve_smul_D_jqModC_mem_regularDifferentials_residueField_of_smul_D_mem_regularDifferentialsBar (solution)
