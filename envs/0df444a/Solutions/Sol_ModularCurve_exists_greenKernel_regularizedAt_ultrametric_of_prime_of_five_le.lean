-- Prove2me | solution 1 for ModularCurve.exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/c3cda6ca-0216-5e5b-85d7-386c6e1b2794

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Theorems.Thm_ModularCurve_exists_uniform_dualGraphCovering_of_prime_of_five_le
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.MultCovering.instAlgebraFbar ModularCurve.MultCovering.instFieldFbar ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.LevelOnePhi.instAddCommGroup instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_fst ModularCurve.MultCovering.ssValue_edgeOf ModularCurve.MultCovering.ChartCtx.mk.sizeOf_spec ModularCurve.MultCovering.ChartCtx.mk.injEq ModularCurve.MultCovering.chart_one ModularCurve.MultCovering.chart_zero AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.MultCovering.AnnCtx.mk.sizeOf_spec ModularCurve.MultCovering.AnnCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.sizeOf_spec ModularCurve.MultCovering.FamCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.injEq ModularCurve.MultCovering.FamCtx.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

open IsLocalRing

private structure CoveringProfile where

  n : ℕ

  m : ℕ

  B : ℕ

  k : ℕ

  Cc : ℝ

variable (pf : CoveringProfile)
variable (A : ValuationSubring (AlgebraicClosure ℚ))
variable (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F]

set_option synthInstance.maxHeartbeats 1600000 in

private structure AdaptedCovering (P₀ : Place (AlgebraicClosure ℚ) F) (p : AlgebraicClosure ℚ)
    {r : ℕ} (s : Fin r → F) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) where

  Fbar : Fin pf.n → Type

  [instField : ∀ i, Field (Fbar i)]

  [instAlg : ∀ i, Algebra (ResidueField A) (Fbar i)]

  chart : ∀ i, ComponentChart A F (Fbar i)

  an : Fin pf.m → Annulus A F

  an' : Fin pf.m → Annulus A F

  src : Fin pf.m → Fin pf.n

  tgt : Fin pf.m → Fin pf.n

  xs : ∀ e, Place (ResidueField A) (Fbar (src e))

  xt : ∀ e, Place (ResidueField A) (Fbar (tgt e))

  T : ∀ i, Place (ResidueField A) (Fbar i) → F

  cuspIdx : Fin pf.n

  hna : IsNonarchimedean (μ : AlgebraicClosure ℚ → ℝ)

  ball : ∀ y : AlgebraicClosure ℚ, y ∈ A ↔ μ y ≤ 1

  pair : ∀ e, (an' e).dom = (an e).dom ∧ (an' e).modulus = (an e).modulus ∧
    ((an e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
    (an' e).param * (an e).param
      = algebraMap (AlgebraicClosure ℚ) F ((an e).modulus : AlgebraicClosure ℚ)

  attached : ∀ e, (an e).IsAttached (chart (src e)) (xs e) ∧ (an' e).IsAttached (chart (tgt e)) (xt e)

  node_end : ∀ i, ∀ x ∈ (chart i).nodes, ∃ e,
    (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
    (⟨tgt e, xt e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩

  end_unique : ∀ i, ∀ x ∈ (chart i).nodes, ∀ E E' : Fin pf.m ⊕ Fin pf.m,
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j))) (fun e => ⟨tgt e, xt e⟩) E
        = ⟨i, x⟩ →
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j))) (fun e => ⟨tgt e, xt e⟩) E'
        = ⟨i, x⟩ → E = E'

  partition : ∀ P : Place (AlgebraicClosure ℚ) F,
    (∃ i, P ∈ (chart i).dom ∧ (∀ j, P ∈ (chart j).dom → j = i) ∧ ∀ e, P ∉ (an e).dom) ∨
    (∃ e, P ∈ (an e).dom ∧ (∀ e', P ∈ (an e').dom → e' = e) ∧ ∀ i, P ∉ (chart i).dom)

  cusp_mem : P₀ ∈ (chart cuspIdx).dom

  basis_norm : ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ p ^ pf.B * c ∈ A ∧ p ^ pf.B * c⁻¹ ∈ A ∧
    ∃ h : c • s l ∈ (chart cuspIdx).integers, (chart cuspIdx).residue ⟨c • s l, h⟩ ≠ 0

  res : ∀ i, HasPrincipalDivisors (ResidueField A) (Fbar i) ∧
    ∀ x : Place (ResidueField A) (Fbar i), x.IsRational

  conn : ∀ i j : Fin pf.n, Relation.ReflTransGen
    (fun a b : Fin pf.n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j

  thick : ∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    p ^ pf.k = ((an e).modulus : AlgebraicClosure ℚ) * a

  disc : ∀ i, ∀ P ∈ (chart i).dom,
    ∃ h : T i ((chart i).placeMap P)
        - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T i ((chart i).placeMap P)))
          ∈ (chart i).integers,
      (chart i).residue ⟨_, h⟩ ≠ 0 ∧ ((chart i).placeMap P).ord ((chart i).residue ⟨_, h⟩) = 1 ∧
      0 < P.ord (T i ((chart i).placeMap P)
        - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T i ((chart i).placeMap P)))) ∧
      ∀ Q ∈ (chart i).dom, (chart i).placeMap Q = (chart i).placeMap P → Q ≠ P →
        Q.ord (T i ((chart i).placeMap P)
          - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T i ((chart i).placeMap P)))) = 0

  anCmp : ∀ e, ∀ P ∈ (an e).dom, ∀ Q ∈ (an e).dom, P ≠ Q →
    (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
    |prox μ (evalVec s P) (evalVec s Q)
        + Real.log (μ (P.evalAt (an e).param - Q.evalAt (an e).param))|
      ≤ pf.Cc * (-Real.log (μ ((an e).modulus : AlgebraicClosure ℚ)))

  chartCmp : ∀ i, ∀ P ∈ (chart i).dom, ∀ Q ∈ (chart i).dom, P ≠ Q →
    (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
    ((chart i).placeMap P = (chart i).placeMap Q →
      |prox μ (evalVec s P) (evalVec s Q)
          + Real.log (μ (P.evalAt (T i ((chart i).placeMap P)) - Q.evalAt (T i ((chart i).placeMap P))))|
        ≤ pf.Cc * (-Real.log (μ p))) ∧
    ((chart i).placeMap P ≠ (chart i).placeMap Q →
      |prox μ (evalVec s P) (evalVec s Q)| ≤ pf.Cc * (-Real.log (μ p)))

  far : ∀ P Q : Place (AlgebraicClosure ℚ) F,
    (∀ i, P ∈ (chart i).dom → Q ∉ (chart i).dom) → (∀ e, P ∈ (an e).dom → Q ∉ (an e).dom) →
    |prox μ (evalVec s P) (evalVec s Q)| ≤ pf.Cc * (-Real.log (μ p))

namespace AdaptedCovering

attribute [scoped instance] instField instAlg

variable {pf A F} {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}

private abbrev cuspChart (Γ : AdaptedCovering pf A F P₀ p s μ) : ComponentChart A F (Γ.Fbar Γ.cuspIdx) :=
  Γ.chart Γ.cuspIdx

private def len (Γ : AdaptedCovering pf A F P₀ p s μ) (e : Fin pf.m) : ℝ :=
  -Real.log (μ ((Γ.an e).modulus : AlgebraicClosure ℚ))

end AdaptedCovering
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff placeMap residue nodes exists_smul_mem pointwise residue_algebraMap ker_residue mapDomain_placeMap placeMap_not_mem_nodes dom"
p2m_open "AlgebraicCurve.ComponentChart"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (C : ComponentChart A F Fbar)

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero {u : C.integers} (hu : C.residue u ≠ 0) : IsUnit u := by
  by_contra hnu
  apply hu
  have hm : u ∈ maximalIdeal C.integers :=
    (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  rw [← C.ker_residue] at hm
  exact hm

p2m_export "AlgebraicCurve.ComponentChart" "isUnit_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.coe_ne_zero_of_residue_ne_zero {u : C.integers} (hu : C.residue u ≠ 0) :
    (u : F) ≠ 0 := by
  intro h0
  apply hu
  have hu0 : u = 0 := Subtype.ext (by simpa using h0)
  rw [hu0, map_zero]

p2m_export "AlgebraicCurve.ComponentChart" "coe_ne_zero_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.exists_inv_mem_residue_ne_zero {u : C.integers} (hu : C.residue u ≠ 0) :
    ∃ hv : (u : F)⁻¹ ∈ C.integers, C.residue ⟨(u : F)⁻¹, hv⟩ ≠ 0 := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp (C.isUnit_of_residue_ne_zero hu)
  have hvF : (u : F) * (v : F) = 1 := by
    have h := congrArg Subtype.val hv
    simpa using h
  have hinvF : (u : F)⁻¹ = (v : F) := inv_eq_of_mul_eq_one_right hvF
  have hmem : (u : F)⁻¹ ∈ C.integers := by rw [hinvF]; exact v.2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨(u : F)⁻¹, hmem⟩ : C.integers) = v := Subtype.ext hinvF
  rw [hsub]
  intro h0
  have h1 : C.residue u * C.residue v = 1 := by rw [← map_mul, hv, map_one]
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

p2m_export "AlgebraicCurve.ComponentChart" "exists_inv_mem_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.absoluteValue_eq_one_of_residue_ne_zero (μ : AbsoluteValue L ℝ)
    (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) {x : L} (hx : algebraMap L F x ∈ C.integers)
    (hres : C.residue ⟨algebraMap L F x, hx⟩ ≠ 0) : μ x = 1 := by
  have hx0 : x ≠ 0 := by
    intro h
    apply C.coe_ne_zero_of_residue_ne_zero hres
    show algebraMap L F x = 0
    rw [h, map_zero]
  have hle : μ x ≤ 1 := (hA x).mp ((C.algebraMap_mem_iff x).mp hx)
  obtain ⟨hm, -⟩ := C.exists_inv_mem_residue_ne_zero hres
  have hinv : algebraMap L F x⁻¹ ∈ C.integers := by
    rw [map_inv₀]
    exact hm
  have hle' : μ x⁻¹ ≤ 1 := (hA x⁻¹).mp ((C.algebraMap_mem_iff x⁻¹).mp hinv)
  have hmul : μ x * μ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have hge : 1 ≤ μ x := by
    have h1 : μ x * μ x⁻¹ ≤ μ x * 1 := mul_le_mul_of_nonneg_left hle' (μ.nonneg x)
    rw [hmul, mul_one] at h1
    exact h1
  exact le_antisymm hle hge

p2m_export "AlgebraicCurve.ComponentChart" "absoluteValue_eq_one_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.absoluteValue_smul_eq_of_residue_ne_zero (μ : AbsoluteValue L ℝ)
    (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) {f : F} {c c' : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (hc' : c' • f ∈ C.integers) (hres' : C.residue ⟨c' • f, hc'⟩ ≠ 0) :
    μ c = μ c' := by
  have hcf : c • f ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hres
  have hcf' : c' • f ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hres'
  have hf0 : f ≠ 0 := fun h => hcf (by rw [h, smul_zero])
  have hc'0 : c' ≠ 0 := fun h => hcf' (by rw [h, zero_smul])
  obtain ⟨hw, hwres⟩ := C.exists_inv_mem_residue_ne_zero hres'
  have hpm : (c • f) * (c' • f)⁻¹ ∈ C.integers := mul_mem hc hw
  have hpres : C.residue ⟨(c • f) * (c' • f)⁻¹, hpm⟩ ≠ 0 := by
    have hsub : (⟨(c • f) * (c' • f)⁻¹, hpm⟩ : C.integers)
        = (⟨c • f, hc⟩ : C.integers) * ⟨(c' • f)⁻¹, hw⟩ := Subtype.ext rfl
    rw [hsub, map_mul]
    exact mul_ne_zero hres hwres
  have hkey : (c • f) * (c' • f)⁻¹ = algebraMap L F (c * c'⁻¹) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_inv, map_mul, map_inv₀,
      mul_mul_mul_comm, mul_inv_cancel₀ hf0, mul_one]
  have hpm' : algebraMap L F (c * c'⁻¹) ∈ C.integers := by rw [← hkey]; exact hpm
  have hsub2 : (⟨algebraMap L F (c * c'⁻¹), hpm'⟩ : C.integers)
      = ⟨(c • f) * (c' • f)⁻¹, hpm⟩ := Subtype.ext hkey.symm
  have hres2 : C.residue ⟨algebraMap L F (c * c'⁻¹), hpm'⟩ ≠ 0 := by
    rw [hsub2]
    exact hpres
  have hone : μ (c * c'⁻¹) = 1 :=
    C.absoluteValue_eq_one_of_residue_ne_zero μ hA hpm' hres2
  have h3 : μ (c * c'⁻¹) * μ c' = 1 * μ c' := by rw [hone]
  rw [← map_mul, mul_assoc, inv_mul_cancel₀ hc'0, mul_one, one_mul] at h3
  exact h3

p2m_export "AlgebraicCurve.ComponentChart" "absoluteValue_smul_eq_of_residue_ne_zero"

open Classical in

private noncomputable def _root_.AlgebraicCurve.ComponentChart.logGaussNorm (μ : AbsoluteValue L ℝ) (f : F) : ℝ :=
  if hf : f ≠ 0 then -Real.log (μ (Classical.choose (C.exists_smul_mem f hf))) else 0

p2m_export "AlgebraicCurve.ComponentChart" "logGaussNorm"
@[scoped simp] private theorem logGaussNorm_zero (μ : AbsoluteValue L ℝ) : C.logGaussNorm μ 0 = 0 :=
  dif_neg fun h => h rfl

private theorem _root_.AlgebraicCurve.ComponentChart.logGaussNorm_eq_neg_log (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {f : F} {c : L} (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0) :
    C.logGaussNorm μ f = -Real.log (μ c) := by
  have hcf : (c • f : F) ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hres
  have hf0 : f ≠ 0 := fun h => hcf (by rw [h, smul_zero])
  simp only [logGaussNorm]
  rw [dif_pos hf0]
  obtain ⟨h₀, hres₀⟩ := Classical.choose_spec (C.exists_smul_mem f hf0)
  rw [C.absoluteValue_smul_eq_of_residue_ne_zero μ hA h₀ hres₀ hc hres]

p2m_export "AlgebraicCurve.ComponentChart" "logGaussNorm_eq_neg_log"

private theorem _root_.AlgebraicCurve.ComponentChart.logGaussNorm_mul (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {f₁ f₂ : F} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) :
    C.logGaussNorm μ (f₁ * f₂) = C.logGaussNorm μ f₁ + C.logGaussNorm μ f₂ := by
  obtain ⟨c₁, hm₁, hr₁⟩ := C.exists_smul_mem f₁ h₁
  obtain ⟨c₂, hm₂, hr₂⟩ := C.exists_smul_mem f₂ h₂
  have hcf₁ : c₁ • f₁ ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hr₁
  have hcf₂ : c₂ • f₂ ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hr₂
  have hc₁ : c₁ ≠ 0 := fun h => hcf₁ (by rw [h, zero_smul])
  have hc₂ : c₂ ≠ 0 := fun h => hcf₂ (by rw [h, zero_smul])
  have hkey : (c₁ * c₂) • (f₁ * f₂) = (c₁ • f₁) * (c₂ • f₂) := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
    ring
  have hmm : (c₁ * c₂) • (f₁ * f₂) ∈ C.integers := by rw [hkey]; exact mul_mem hm₁ hm₂
  have hrr : C.residue ⟨(c₁ * c₂) • (f₁ * f₂), hmm⟩ ≠ 0 := by
    have hsub : (⟨(c₁ * c₂) • (f₁ * f₂), hmm⟩ : C.integers)
        = (⟨c₁ • f₁, hm₁⟩ : C.integers) * ⟨c₂ • f₂, hm₂⟩ := Subtype.ext hkey
    rw [hsub, map_mul]
    exact mul_ne_zero hr₁ hr₂
  rw [C.logGaussNorm_eq_neg_log μ hA hmm hrr, C.logGaussNorm_eq_neg_log μ hA hm₁ hr₁,
    C.logGaussNorm_eq_neg_log μ hA hm₂ hr₂, map_mul,
    Real.log_mul (μ.ne_zero hc₁) (μ.ne_zero hc₂)]
  ring

p2m_export "AlgebraicCurve.ComponentChart" "logGaussNorm_mul"

private theorem _root_.AlgebraicCurve.ComponentChart.absoluteValue_le_of_smul_mem (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {f : F} {c d : L} (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (hd : d • f ∈ C.integers) : μ d ≤ μ c := by
  have hcf : c • f ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hres
  have hf0 : f ≠ 0 := fun h => hcf (by rw [h, smul_zero])
  have hc0 : c ≠ 0 := fun h => hcf (by rw [h, zero_smul])
  obtain ⟨hw, -⟩ := C.exists_inv_mem_residue_ne_zero hres
  have hpm : (d • f) * (c • f)⁻¹ ∈ C.integers := mul_mem hd hw
  have hkey : (d • f) * (c • f)⁻¹ = algebraMap L F (d * c⁻¹) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_inv, map_mul, map_inv₀,
      mul_mul_mul_comm, mul_inv_cancel₀ hf0, mul_one]
  have hpm' : algebraMap L F (d * c⁻¹) ∈ C.integers := by rw [← hkey]; exact hpm
  have hle : μ (d * c⁻¹) ≤ 1 := (hA _).mp ((C.algebraMap_mem_iff _).mp hpm')
  rw [map_mul, map_inv₀, ← div_eq_mul_inv] at hle
  exact (div_le_one (μ.pos hc0)).mp hle

p2m_export "AlgebraicCurve.ComponentChart" "absoluteValue_le_of_smul_mem"

private theorem _root_.AlgebraicCurve.ComponentChart.logGaussNorm_add_le (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {f₁ f₂ : F} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) (h₁₂ : f₁ + f₂ ≠ 0) :
    C.logGaussNorm μ (f₁ + f₂) ≤ max (C.logGaussNorm μ f₁) (C.logGaussNorm μ f₂) := by
  suffices key : ∀ {g₁ g₂ : F} {c₁ c₂ : L} (hm₁ : c₁ • g₁ ∈ C.integers)
      (_ : C.residue ⟨c₁ • g₁, hm₁⟩ ≠ 0) (hm₂ : c₂ • g₂ ∈ C.integers)
      (_ : C.residue ⟨c₂ • g₂, hm₂⟩ ≠ 0), g₁ + g₂ ≠ 0 → μ c₂ ≤ μ c₁ →
      C.logGaussNorm μ (g₁ + g₂) ≤ C.logGaussNorm μ g₂ by
    obtain ⟨c₁, hm₁, hr₁⟩ := C.exists_smul_mem f₁ h₁
    obtain ⟨c₂, hm₂, hr₂⟩ := C.exists_smul_mem f₂ h₂
    rcases le_total (μ c₂) (μ c₁) with hle | hle
    · exact (key hm₁ hr₁ hm₂ hr₂ h₁₂ hle).trans (le_max_right _ _)
    · have h := key hm₂ hr₂ hm₁ hr₁ (by rwa [add_comm]) hle
      rw [add_comm] at h
      exact h.trans (le_max_left _ _)
  intro g₁ g₂ c₁ c₂ hm₁ hr₁ hm₂ hr₂ hg hle
  have hcg₁ : c₁ • g₁ ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hr₁
  have hc₁ : c₁ ≠ 0 := fun h => hcg₁ (by rw [h, zero_smul])
  have hcg₂ : c₂ • g₂ ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hr₂
  have hc₂ : c₂ ≠ 0 := fun h => hcg₂ (by rw [h, zero_smul])
  have hq : c₂ * c₁⁻¹ ∈ A := by
    rw [hA, map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (div_le_one (μ.pos hc₁)).mpr hle
  have hm₂₁ : c₂ • g₁ ∈ C.integers := by
    have h : c₂ • g₁ = algebraMap L F (c₂ * c₁⁻¹) * (c₁ • g₁) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, mul_assoc,
        inv_mul_cancel_left₀ ((map_ne_zero (algebraMap L F)).mpr hc₁)]
    rw [h]
    exact mul_mem ((C.algebraMap_mem_iff _).mpr hq) hm₁
  have hsum : c₂ • (g₁ + g₂) ∈ C.integers := by
    rw [smul_add]
    exact add_mem hm₂₁ hm₂
  obtain ⟨c, hm, hr⟩ := C.exists_smul_mem (g₁ + g₂) hg
  have hle' : μ c₂ ≤ μ c := C.absoluteValue_le_of_smul_mem μ hA hm hr hsum
  rw [C.logGaussNorm_eq_neg_log μ hA hm hr, C.logGaussNorm_eq_neg_log μ hA hm₂ hr₂, neg_le_neg_iff]
  exact Real.log_le_log (μ.pos hc₂) hle'

p2m_export "AlgebraicCurve.ComponentChart" "logGaussNorm_add_le"
end ComponentChart
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
namespace AdaptedCovering
p2m_open "AlgebraicCurve"

open IsLocalRing

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)} {F : Type} [Field F]
  [Algebra (AlgebraicClosure ℚ) F] {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}

private theorem abs_log_le_of_pow_mul_mem (hball : ∀ y : AlgebraicClosure ℚ, y ∈ A ↔ μ y ≤ 1)
    (hp : 0 < μ p) {c : AlgebraicClosure ℚ} (hc : c ≠ 0) {B : ℕ} (h₁ : p ^ B * c ∈ A)
    (h₂ : p ^ B * c⁻¹ ∈ A) : |Real.log (μ c)| ≤ B * (-Real.log (μ p)) := by
  have hpB : 0 < μ p ^ B := pow_pos hp B
  have hc' : 0 < μ c := μ.pos hc
  have h₁' : μ p ^ B * μ c ≤ 1 := by
    have h := (hball _).mp h₁
    rwa [map_mul, map_pow] at h
  have h₂' : μ p ^ B * (μ c)⁻¹ ≤ 1 := by
    have h := (hball _).mp h₂
    rwa [map_mul, map_pow, map_inv₀] at h
  have hlog₁ := Real.log_nonpos (mul_nonneg hpB.le hc'.le) h₁'
  have hlog₂ := Real.log_nonpos (mul_nonneg hpB.le (inv_nonneg.mpr hc'.le)) h₂'
  rw [Real.log_mul hpB.ne' hc'.ne', Real.log_pow] at hlog₁
  rw [Real.log_mul hpB.ne' (inv_ne_zero hc'.ne'), Real.log_inv, Real.log_pow] at hlog₂
  rw [abs_le]
  constructor <;> linarith

private theorem abs_logGaussNorm_cuspChart_le (Γ : AdaptedCovering pf A F P₀ p s μ) (hp : 0 < μ p)
    (l : Fin r) : |Γ.cuspChart.logGaussNorm μ (s l)| ≤ pf.B * (-Real.log (μ p)) := by
  obtain ⟨c, hc, h₁, h₂, hmem, hres⟩ := Γ.basis_norm l
  rw [Γ.cuspChart.logGaussNorm_eq_neg_log μ Γ.ball hmem hres, abs_neg]
  exact abs_log_le_of_pow_mul_mem Γ.ball hp hc h₁ h₂

private theorem logGaussNorm_cuspChart_mul (Γ : AdaptedCovering pf A F P₀ p s μ) {f₁ f₂ : F} (h₁ : f₁ ≠ 0)
    (h₂ : f₂ ≠ 0) :
    Γ.cuspChart.logGaussNorm μ (f₁ * f₂)
      = Γ.cuspChart.logGaussNorm μ f₁ + Γ.cuspChart.logGaussNorm μ f₂ :=
  Γ.cuspChart.logGaussNorm_mul μ Γ.ball h₁ h₂

end AlgebraicCurve.AdaptedCovering
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart"
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart"

namespace SimpleGraph
p2m_export "SimpleGraph" "edgeFinset Dart neighborFinset dart_edge_fiber_card ball loopless mem_edgeSet dart_fst_fiber Embedding neighborFinset_eq_filter dartOfNeighborSet_injective Reachable.refl Adj.reachable Connected mem_edgeFinset support mem_neighborFinset Walk Partition symm Walk.edges_cons between Path Adj structure degree adj_symm mem_neighborSet Reachable neighborSet edge"
p2m_open "SimpleGraph"

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private noncomputable def _root_.SimpleGraph.lapW (w : Sym2 V → ℝ) (g : V → ℝ) (v : V) : ℝ :=
  ∑ u ∈ G.neighborFinset v, w s(v, u) * (g v - g u)

p2m_export "SimpleGraph" "lapW"
omit [DecidableEq V] in
private theorem _root_.SimpleGraph.lapW_add (w : Sym2 V → ℝ) (g h : V → ℝ) (v : V) :
    G.lapW w (g + h) v = G.lapW w g v + G.lapW w h v := by
  unfold lapW
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Pi.add_apply]
  ring

p2m_export "SimpleGraph" "lapW_add"
omit [DecidableEq V] in
private theorem _root_.SimpleGraph.lapW_smul (w : Sym2 V → ℝ) (c : ℝ) (g : V → ℝ) (v : V) :
    G.lapW w (c • g) v = c * G.lapW w g v := by
  unfold lapW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

p2m_export "SimpleGraph" "lapW_smul"

private noncomputable def _root_.SimpleGraph.groundedOp (w : Sym2 V → ℝ) (v₀ : V) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun g v := if v = v₀ then g v₀ else G.lapW w g v
  map_add' g h := by
    funext v
    simp only [Pi.add_apply]
    split_ifs
    · rfl
    · exact G.lapW_add w g h v
  map_smul' c g := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · exact G.lapW_smul w c g v

p2m_export "SimpleGraph" "groundedOp"
omit [DecidableEq V] in

private theorem _root_.SimpleGraph.two_mul_sum_mul_lapW (w : Sym2 V → ℝ) (g : V → ℝ) :
    2 * ∑ v, g v * G.lapW w g v
      = ∑ v, ∑ u, if G.Adj v u then w s(v, u) * (g v - g u) ^ 2 else 0 := by
  have hexp : ∀ v, g v * G.lapW w g v
      = ∑ u, if G.Adj v u then w s(v, u) * (g v - g u) * g v else 0 := by
    intro v
    unfold lapW
    rw [Finset.mul_sum, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs
    · ring
    · rfl
  have hswap : ∑ v, ∑ u, (if G.Adj v u then w s(v, u) * (g v - g u) * g v else 0)
      = ∑ v, ∑ u, (if G.Adj v u then w s(v, u) * (g u - g v) * g u else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj v u
    · rw [if_pos h, if_pos (G.adj_symm h), Sym2.eq_swap]
    · rw [if_neg h, if_neg (fun h' => h (G.adj_symm h'))]
  simp_rw [hexp]
  rw [two_mul]
  nth_rewrite 2 [hswap]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs
  · ring
  · simp

p2m_export "SimpleGraph" "two_mul_sum_mul_lapW"

private theorem _root_.SimpleGraph.eq_of_adj_of_lapW_eq_zero (w : Sym2 V → ℝ) (hw : ∀ e ∈ G.edgeFinset, 0 < w e)
    (v₀ : V) (g : V → ℝ) (h0 : g v₀ = 0) (hlap : ∀ v, v ≠ v₀ → G.lapW w g v = 0) :
    ∀ u v, G.Adj u v → g u = g v := by
  have hsum : ∑ v, g v * G.lapW w g v = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v = v₀
    · rw [hv, h0, zero_mul]
    · rw [hlap v hv, mul_zero]
  have henergy := G.two_mul_sum_mul_lapW w g
  rw [hsum, mul_zero] at henergy
  have hnonneg : ∀ v u, 0 ≤ (if G.Adj v u then w s(v, u) * (g v - g u) ^ 2 else 0) := by
    intro v u
    split_ifs with h
    · exact mul_nonneg (hw _ (G.mem_edgeFinset.mpr ((G.mem_edgeSet).mpr h))).le (sq_nonneg _)
    · exact le_rfl
  have hrow : ∀ v ∈ (Finset.univ : Finset V),
      ∑ u, (if G.Adj v u then w s(v, u) * (g v - g u) ^ 2 else 0) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun v _ => Finset.sum_nonneg fun u _ => hnonneg v u).mp
      henergy.symm
  intro u v huv
  have hu := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hnonneg u x).mp
    (hrow u (Finset.mem_univ _)) v (Finset.mem_univ _)
  rw [if_pos huv] at hu
  have hwpos : 0 < w s(u, v) := hw _ (G.mem_edgeFinset.mpr ((G.mem_edgeSet).mpr huv))
  have hsq : (g u - g v) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hu with h | h
    · exact absurd h hwpos.ne'
    · exact h
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

p2m_export "SimpleGraph" "eq_of_adj_of_lapW_eq_zero"

private theorem _root_.SimpleGraph.groundedOp_injective (hG : G.Connected) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeFinset, 0 < w e) (v₀ : V) :
    Function.Injective (G.groundedOp w v₀) := by
  refine (injective_iff_map_eq_zero _).mpr fun g hg => ?_
  have h0 : g v₀ = 0 := by
    have := congrFun hg v₀
    simpa [groundedOp] using this
  have hlap : ∀ v, v ≠ v₀ → G.lapW w g v = 0 := by
    intro v hv
    have := congrFun hg v
    simpa [groundedOp, hv] using this
  have hadj := G.eq_of_adj_of_lapW_eq_zero w hw v₀ g h0 hlap
  funext v
  obtain ⟨p⟩ := hG.preconnected v v₀
  have hconst : ∀ {a c : V} (q : G.Walk a c), g a = g c := by
    intro a c q
    induction q with
    | nil => rfl
    | cons hA _ ih => exact (hadj _ _ hA).trans ih
  rw [Pi.zero_apply, hconst p, h0]

p2m_export "SimpleGraph" "groundedOp_injective"

private theorem existsUnique_grounded {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeFinset, 0 < w e) (v₀ : V) (b : V → ℝ) :
    ∃! g : V → ℝ, g v₀ = 0 ∧
      ∀ v, v ≠ v₀ → ∑ u ∈ G.neighborFinset v, w s(v, u) * (g v - g u) = b v := by
  have hinj := G.groundedOp_injective hG w hw v₀
  have hsurj : Function.Surjective (G.groundedOp w v₀) := LinearMap.surjective_of_injective hinj
  obtain ⟨g, hg⟩ := hsurj (fun v => if v = v₀ then 0 else b v)
  have hg0 : g v₀ = 0 := by
    have := congrFun hg v₀
    simpa [groundedOp] using this
  refine ⟨g, ⟨hg0, fun v hv => ?_⟩, fun g' hg' => ?_⟩
  · have := congrFun hg v
    simpa [groundedOp, hv, lapW] using this
  · apply hinj
    funext v
    show (if v = v₀ then g' v₀ else G.lapW w g' v) = (if v = v₀ then g v₀ else G.lapW w g v)
    by_cases hv : v = v₀
    · rw [if_pos hv, if_pos hv, hg'.1, hg0]
    · rw [if_neg hv, if_neg hv]
      show ∑ u ∈ G.neighborFinset v, w s(v, u) * (g' v - g' u)
        = ∑ u ∈ G.neighborFinset v, w s(v, u) * (g v - g u)
      rw [hg'.2 v hv]
      have := congrFun hg v
      simp only [groundedOp, LinearMap.coe_mk, AddHom.coe_mk, if_neg hv] at this
      exact this.symm

omit [DecidableEq V] in

private theorem _root_.SimpleGraph.sum_dart_edge_eq_two_mul (F : Sym2 V → ℝ) :
    ∑ d : G.Dart, F d.edge = 2 * ∑ e ∈ G.edgeFinset, F e := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset G.Dart)) (t := G.edgeFinset)
    (g := fun d : G.Dart => d.edge)
    (fun d _ => G.mem_edgeFinset.mpr d.edge_mem) F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_const, G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he), nsmul_eq_mul]
  norm_num

p2m_export "SimpleGraph" "sum_dart_edge_eq_two_mul"

private theorem _root_.SimpleGraph.sum_dart_edge_eq_sum_sum (F : Sym2 V → ℝ) :
    ∑ d : G.Dart, F d.edge = ∑ v, ∑ u ∈ G.neighborFinset v, F s(v, u) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset G.Dart)) (t := Finset.univ)
    (g := fun d : G.Dart => d.fst) (fun d _ => Finset.mem_univ _) (fun d => F d.edge)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [G.dart_fst_fiber v, Finset.sum_image (fun x _ y _ h => G.dartOfNeighborSet_injective v h)]
  show ∑ x : G.neighborSet v, F s(v, (x : V)) = _
  rw [← Finset.sum_subtype (G.neighborFinset v) (p := fun u => u ∈ G.neighborSet v)
    (fun u => (G.mem_neighborFinset v u).trans (G.mem_neighborSet v u).symm)
    (fun u => F s(v, u))]

p2m_export "SimpleGraph" "sum_dart_edge_eq_sum_sum"

private theorem _root_.SimpleGraph.sum_sum_neighborFinset_eq_two_mul (F : Sym2 V → ℝ) :
    ∑ v, ∑ u ∈ G.neighborFinset v, F s(v, u) = 2 * ∑ e ∈ G.edgeFinset, F e := by
  rw [← G.sum_dart_edge_eq_sum_sum F, G.sum_dart_edge_eq_two_mul F]

p2m_export "SimpleGraph" "sum_sum_neighborFinset_eq_two_mul"

private def absDiff (g : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => |g x - g y|, fun x y => abs_sub_comm (g x) (g y)⟩

omit [Fintype V] [DecidableEq V] in
@[scoped simp] private theorem absDiff_mk (g : V → ℝ) (x y : V) : absDiff g s(x, y) = |g x - g y| := rfl

private theorem _root_.SimpleGraph.sum_edgeFinset_mul_sq_eq (w : Sym2 V → ℝ) (g : V → ℝ) :
    ∑ e ∈ G.edgeFinset, w e * absDiff g e ^ 2 = ∑ v, g v * G.lapW w g v := by
  have h2 := G.two_mul_sum_mul_lapW w g
  have hnbr : ∑ v, ∑ u, (if G.Adj v u then w s(v, u) * (g v - g u) ^ 2 else 0)
      = ∑ v, ∑ u ∈ G.neighborFinset v, w s(v, u) * absDiff g s(v, u) ^ 2 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs
    · simp [sq_abs]
    · rfl
  have h3 : ∑ v, ∑ u ∈ G.neighborFinset v, w s(v, u) * absDiff g s(v, u) ^ 2
      = 2 * ∑ e ∈ G.edgeFinset, w e * absDiff g e ^ 2 :=
    G.sum_sum_neighborFinset_eq_two_mul (fun e => w e * absDiff g e ^ 2)
  rw [hnbr, h3] at h2
  linarith

p2m_export "SimpleGraph" "sum_edgeFinset_mul_sq_eq"
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

private theorem _root_.SimpleGraph.abs_sub_le_sum_edges (g : V → ℝ) {a c : V} (p : G.Walk a c) :
    |g a - g c| ≤ (p.edges.map (absDiff g)).sum := by
  induction p with
  | nil => simp
  | @cons x y z hxy q ih =>
    rw [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, absDiff_mk]
    calc |g x - g z| = |(g x - g y) + (g y - g z)| := by ring_nf
      _ ≤ |g x - g y| + |g y - g z| := abs_add_le _ _
      _ ≤ |g x - g y| + (q.edges.map (absDiff g)).sum := by linarith

p2m_export "SimpleGraph" "abs_sub_le_sum_edges"

private theorem _root_.SimpleGraph.sq_le_resistance_mul_energy (hG : G.Connected) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeFinset, 0 < w e) (v₀ : V) (g : V → ℝ) (hg₀ : g v₀ = 0) (x : V) :
    g x ^ 2 ≤ (∑ e ∈ G.edgeFinset, (w e)⁻¹) * ∑ e ∈ G.edgeFinset, w e * absDiff g e ^ 2 := by
  classical
  refine (hG.preconnected x v₀).elim_path fun q => ?_
  set P : Finset (Sym2 V) := (q : G.Walk x v₀).edges.toFinset with hP
  have hPsub : P ⊆ G.edgeFinset := by
    intro e he
    rw [hP, List.mem_toFinset] at he
    exact G.mem_edgeFinset.mpr ((q : G.Walk x v₀).edges_subset_edgeSet he)
  have hwP : ∀ e ∈ P, 0 < w e := fun e he => hw e (hPsub he)

  have htel : |g x| ≤ ∑ e ∈ P, absDiff g e := by
    have h := G.abs_sub_le_sum_edges g (q : G.Walk x v₀)
    rw [hg₀, sub_zero] at h
    rw [hP, List.sum_toFinset _ q.2.edges_nodup]
    exact h

  have hCS : (∑ e ∈ P, absDiff g e) ^ 2
      ≤ (∑ e ∈ P, (w e)⁻¹) * ∑ e ∈ P, w e * absDiff g e ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P (fun e he => (inv_pos.mpr (hwP e he)).le)
      (fun e he => mul_nonneg (hwP e he).le (sq_nonneg _)) (fun e he => ?_)
    rw [← mul_assoc, inv_mul_cancel₀ (hwP e he).ne', one_mul]

  have hR : ∑ e ∈ P, (w e)⁻¹ ≤ ∑ e ∈ G.edgeFinset, (w e)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hPsub fun e he _ => (inv_pos.mpr (hw e he)).le
  have hE : ∑ e ∈ P, w e * absDiff g e ^ 2 ≤ ∑ e ∈ G.edgeFinset, w e * absDiff g e ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hPsub fun e he _ => mul_nonneg (hw e he).le (sq_nonneg _)
  have hE0 : 0 ≤ ∑ e ∈ P, w e * absDiff g e ^ 2 :=
    Finset.sum_nonneg fun e he => mul_nonneg (hwP e he).le (sq_nonneg _)
  have hR0 : 0 ≤ ∑ e ∈ G.edgeFinset, (w e)⁻¹ :=
    Finset.sum_nonneg fun e he => (inv_pos.mpr (hw e he)).le
  calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ e ∈ P, absDiff g e) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) htel 2
    _ ≤ (∑ e ∈ P, (w e)⁻¹) * ∑ e ∈ P, w e * absDiff g e ^ 2 := hCS
    _ ≤ (∑ e ∈ G.edgeFinset, (w e)⁻¹) * ∑ e ∈ G.edgeFinset, w e * absDiff g e ^ 2 :=
        mul_le_mul hR hE hE0 hR0

p2m_export "SimpleGraph" "sq_le_resistance_mul_energy"

private theorem abs_apply_le_of_grounded {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeFinset, 0 < w e) (v₀ : V) (b g : V → ℝ) (hg₀ : g v₀ = 0)
    (hg : ∀ v, v ≠ v₀ → ∑ u ∈ G.neighborFinset v, w s(v, u) * (g v - g u) = b v) (v : V) :
    |g v| ≤ (∑ e ∈ G.edgeFinset, (w e)⁻¹) * ∑ u ∈ Finset.univ.erase v₀, |b u| := by
  classical
  set R : ℝ := ∑ e ∈ G.edgeFinset, (w e)⁻¹ with hRdef
  set B : ℝ := ∑ u ∈ Finset.univ.erase v₀, |b u| with hBdef
  set E : ℝ := ∑ e ∈ G.edgeFinset, w e * absDiff g e ^ 2 with hEdef
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun e he => (inv_pos.mpr (hw e he)).le
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun u _ => abs_nonneg _

  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun u => |g u|) ⟨v, Finset.mem_univ _⟩
  set M : ℝ := |g m| with hMdef
  have hMv : ∀ u, |g u| ≤ M := fun u => hm u (Finset.mem_univ _)
  have hM0 : 0 ≤ M := abs_nonneg _

  have hEeq : E = ∑ u ∈ Finset.univ.erase v₀, g u * b u := by
    rw [hEdef, G.sum_edgeFinset_mul_sq_eq w g, ← Finset.add_sum_erase _ _ (Finset.mem_univ v₀),
      hg₀, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [show G.lapW w g u = b u from hg u (Finset.ne_of_mem_erase hu)]
  have hEle : E ≤ M * B := by
    rw [hEeq, hBdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    calc g u * b u ≤ |g u * b u| := le_abs_self _
      _ = |g u| * |b u| := abs_mul _ _
      _ ≤ M * |b u| := mul_le_mul_of_nonneg_right (hMv u) (abs_nonneg _)

  have hsq : M ^ 2 ≤ R * E := by
    rw [hMdef, sq_abs]
    exact G.sq_le_resistance_mul_energy hG w hw v₀ g hg₀ m

  have hMle : M ≤ R * B := by
    rcases hM0.lt_or_eq with hpos | hzero
    · have h1 : M * M ≤ (R * B) * M := by
        calc M * M = M ^ 2 := (sq M).symm
          _ ≤ R * E := hsq
          _ ≤ R * (M * B) := mul_le_mul_of_nonneg_left hEle hR0
          _ = (R * B) * M := by ring
      exact le_of_mul_le_mul_right h1 hpos
    · rw [← hzero]
      exact mul_nonneg hR0 hB0
  exact (hMv v).trans hMle

end SimpleGraph
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace ReductionGraph

section Skeleton

variable {V E : Type*} (src tgt : E → V) (ℓ : E → ℝ)

private def OnSkeleton : V ⊕ (E × ℝ) → Prop
  | Sum.inl _ => True
  | Sum.inr p => 0 ≤ p.2 ∧ p.2 ≤ ℓ p.1

private def piece : V ⊕ (E × ℝ) → V ⊕ E := Sum.map id Prod.fst

@[scoped simp] private theorem onSkeleton_inl (v : V) : OnSkeleton ℓ (Sum.inl v : V ⊕ (E × ℝ)) := trivial

private theorem onSkeleton_inr_iff (p : E × ℝ) :
    OnSkeleton ℓ (Sum.inr p : V ⊕ (E × ℝ)) ↔ 0 ≤ p.2 ∧ p.2 ≤ ℓ p.1 := Iff.rfl

@[scoped simp] private theorem piece_inl (v : V) : piece (Sum.inl v : V ⊕ (E × ℝ)) = Sum.inl v := rfl

@[scoped simp] private theorem piece_inr (p : E × ℝ) : piece (Sum.inr p : V ⊕ (E × ℝ)) = Sum.inr p.1 := rfl

variable [DecidableEq V]

private def vertexWeight : V ⊕ (E × ℝ) → V → ℝ
  | Sum.inl v, u => if u = v then 1 else 0
  | Sum.inr p, u => (if u = src p.1 then (ℓ p.1 - p.2) / ℓ p.1 else 0) +
      (if u = tgt p.1 then p.2 / ℓ p.1 else 0)

@[scoped simp] private theorem vertexWeight_inl (v u : V) :
    vertexWeight src tgt ℓ (Sum.inl v) u = if u = v then 1 else 0 := rfl

@[scoped simp] private theorem vertexWeight_inr (p : E × ℝ) (u : V) :
    vertexWeight src tgt ℓ (Sum.inr p) u =
      (if u = src p.1 then (ℓ p.1 - p.2) / ℓ p.1 else 0) + (if u = tgt p.1 then p.2 / ℓ p.1 else 0) :=
  rfl

private theorem vertexWeight_nonneg {a : V ⊕ (E × ℝ)} (ha : OnSkeleton ℓ a) (u : V) :
    0 ≤ vertexWeight src tgt ℓ a u := by
  cases a with
  | inl v =>
    rw [vertexWeight_inl]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | inr p =>
    obtain ⟨h0, h1⟩ := ha
    have hℓ : 0 ≤ ℓ p.1 := h0.trans h1
    rw [vertexWeight_inr]
    refine add_nonneg ?_ ?_
    · split_ifs
      · exact div_nonneg (sub_nonneg.mpr h1) hℓ
      · exact le_rfl
    · split_ifs
      · exact div_nonneg h0 hℓ
      · exact le_rfl

variable [Fintype V]

private theorem sum_vertexWeight_inl (v : V) : ∑ u, vertexWeight src tgt ℓ (Sum.inl v) u = 1 := by
  simp only [vertexWeight_inl, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem sum_vertexWeight_inr (p : E × ℝ) :
    ∑ u, vertexWeight src tgt ℓ (Sum.inr p) u = ℓ p.1 / ℓ p.1 := by
  simp only [vertexWeight_inr, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← add_div, sub_add_cancel]

private theorem sum_vertexWeight_le_one {a : V ⊕ (E × ℝ)} (ha : OnSkeleton ℓ a) :
    ∑ u, vertexWeight src tgt ℓ a u ≤ 1 := by
  cases a with
  | inl v => rw [sum_vertexWeight_inl]
  | inr p =>
    rw [sum_vertexWeight_inr]
    exact div_self_le_one _

private def pairPotential (J : V → V → ℝ) (a b : V ⊕ (E × ℝ)) : ℝ :=
  ∑ v, ∑ u, vertexWeight src tgt ℓ a v * vertexWeight src tgt ℓ b u * J v u

variable (J : V → V → ℝ)

private theorem pairPotential_inl_left (v : V) (b : V ⊕ (E × ℝ)) :
    pairPotential src tgt ℓ J (Sum.inl v) b = ∑ u, vertexWeight src tgt ℓ b u * J v u := by
  unfold pairPotential
  rw [Finset.sum_eq_single v]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [vertexWeight_inl, if_pos rfl, one_mul]
  · intro v' _ hv'
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [vertexWeight_inl, if_neg hv', zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ v) h

private theorem pairPotential_inl_inl (v u : V) :
    pairPotential src tgt ℓ J (Sum.inl v) (Sum.inl u) = J v u := by
  rw [pairPotential_inl_left, Finset.sum_eq_single u]
  · rw [vertexWeight_inl, if_pos rfl, one_mul]
  · intro u' _ hu'
    rw [vertexWeight_inl, if_neg hu', zero_mul]
  · intro h
    exact absurd (Finset.mem_univ u) h

private theorem pairPotential_inr_left (p : E × ℝ) (b : V ⊕ (E × ℝ)) :
    pairPotential src tgt ℓ J (Sum.inr p) b =
      (ℓ p.1 - p.2) / ℓ p.1 * pairPotential src tgt ℓ J (Sum.inl (src p.1)) b +
        p.2 / ℓ p.1 * pairPotential src tgt ℓ J (Sum.inl (tgt p.1)) b := by
  rw [pairPotential_inl_left, pairPotential_inl_left]
  unfold pairPotential
  simp only [vertexWeight_inr, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  · rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  · rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

private theorem abs_pairPotential_le {R : ℝ} (hJ : ∀ v u, |J v u| ≤ R) {a b : V ⊕ (E × ℝ)}
    (ha : OnSkeleton ℓ a) (hb : OnSkeleton ℓ b) :
    |pairPotential src tgt ℓ J a b| ≤ R := by
  have hR : 0 ≤ R := by
    have v : V := Sum.elim id (fun p => src p.1) a
    exact (abs_nonneg _).trans (hJ v v)
  have hwa := vertexWeight_nonneg src tgt ℓ ha
  have hwb := vertexWeight_nonneg src tgt ℓ hb
  unfold pairPotential
  calc |∑ v, ∑ u, vertexWeight src tgt ℓ a v * vertexWeight src tgt ℓ b u * J v u|
      ≤ ∑ v, |∑ u, vertexWeight src tgt ℓ a v * vertexWeight src tgt ℓ b u * J v u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, ∑ u, |vertexWeight src tgt ℓ a v * vertexWeight src tgt ℓ b u * J v u| :=
        Finset.sum_le_sum fun v _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, ∑ u, vertexWeight src tgt ℓ a v * vertexWeight src tgt ℓ b u * R := by
        refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun u _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hwa v), abs_of_nonneg (hwb u)]
        exact mul_le_mul_of_nonneg_left (hJ v u) (mul_nonneg (hwa v) (hwb u))
    _ = (∑ v, vertexWeight src tgt ℓ a v) * (∑ u, vertexWeight src tgt ℓ b u) * R := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.sum_mul]
    _ ≤ R := by
        have h1 := sum_vertexWeight_le_one src tgt ℓ ha
        have h2 := sum_vertexWeight_le_one src tgt ℓ hb
        have h0b : 0 ≤ ∑ u, vertexWeight src tgt ℓ b u := Finset.sum_nonneg fun u _ => hwb u
        exact mul_le_of_le_one_left hR (mul_le_one₀ h1 h0b h2)

end Skeleton
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph"

section Ground

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V) (ℓ : E → ℝ)

private def adjGraph : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ he => he.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private scoped instance adjGraph.instDecidableRelAdj : DecidableRel (adjGraph src tgt).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)))

p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph"

private def conductance (z : Sym2 V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => s(src e, tgt e) = z), (ℓ e)⁻¹

private theorem conductance_pos (hℓ : ∀ e, 0 < ℓ e) {z : Sym2 V} (hz : z ∈ (adjGraph src tgt).edgeFinset) :
    0 < conductance src tgt ℓ z := by
  induction z using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hz
    obtain ⟨-, e, he⟩ := hz
    unfold conductance
    refine Finset.sum_pos (fun e _ => inv_pos.mpr (hℓ e)) ⟨e, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]

private theorem sum_conductance_mul_sub_eq (g : V → ℝ) (v : V) :
    ∑ u ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u) * (g v - g u)
      = ∑ e ∈ Finset.univ.filter (fun e => src e = v), (ℓ e)⁻¹ * (g v - g (tgt e))
        + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), (ℓ e)⁻¹ * (g v - g (src e)) := by
  have hL : ∑ u ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u) * (g v - g u)
      = ∑ u, conductance src tgt ℓ s(v, u) * (g v - g u) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    by_cases huv : u = v
    · rw [huv, sub_self, mul_zero]
    · have hne : ¬ (adjGraph src tgt).Adj v u := by rwa [SimpleGraph.mem_neighborFinset] at hu
      have hempty : Finset.univ.filter (fun e => s(src e, tgt e) = s(v, u)) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun e _ he =>
          hne (And.intro (Ne.symm huv) (Exists.intro e (Sym2.eq_iff.mp he)))
      show (∑ e ∈ Finset.univ.filter (fun e => s(src e, tgt e) = s(v, u)), (ℓ e)⁻¹) * (g v - g u) = 0
      rw [hempty, Finset.sum_empty, zero_mul]
  have h1 : ∑ e ∈ Finset.univ.filter (fun e => src e = v), (ℓ e)⁻¹ * (g v - g (tgt e))
      = ∑ u, (∑ e ∈ Finset.univ.filter (fun e => src e = v ∧ tgt e = u), (ℓ e)⁻¹) * (g v - g u) := by
    rw [← Finset.sum_fiberwise (Finset.univ.filter fun e => src e = v) tgt
      (fun e => (ℓ e)⁻¹ * (g v - g (tgt e)))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul, Finset.filter_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨-, -, rfl⟩ := Finset.mem_filter.mp he
    rfl
  have h2 : ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), (ℓ e)⁻¹ * (g v - g (src e))
      = ∑ u, (∑ e ∈ Finset.univ.filter (fun e => tgt e = v ∧ src e = u), (ℓ e)⁻¹) * (g v - g u) := by
    rw [← Finset.sum_fiberwise (Finset.univ.filter fun e => tgt e = v) src
      (fun e => (ℓ e)⁻¹ * (g v - g (src e)))]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_mul, Finset.filter_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨-, -, rfl⟩ := Finset.mem_filter.mp he
    rfl
  have h3 : ∀ u, conductance src tgt ℓ s(v, u) * (g v - g u)
      = ((∑ e ∈ Finset.univ.filter (fun e => src e = v ∧ tgt e = u), (ℓ e)⁻¹)
          + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v ∧ src e = u), (ℓ e)⁻¹) * (g v - g u) := by
    intro u
    classical
    by_cases huv : u = v
    · rw [huv, sub_self, mul_zero, mul_zero]
    · have hdisj : Disjoint (Finset.univ.filter (fun e => src e = v ∧ tgt e = u))
          (Finset.univ.filter (fun e => tgt e = v ∧ src e = u)) :=
        Finset.disjoint_filter.mpr fun e _ h h' => huv (h.2.symm.trans h'.1)
      rw [← Finset.sum_union hdisj]
      unfold conductance
      congr 1
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Sym2.eq_iff]
      exact or_congr Iff.rfl and_comm
  rw [hL, h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← add_mul]
  exact h3 u

private theorem sum_inv_conductance_le (hℓ : ∀ e, 0 < ℓ e) :
    ∑ z ∈ (adjGraph src tgt).edgeFinset, (conductance src tgt ℓ z)⁻¹ ≤ ∑ e, ℓ e := by
  have key : ∀ z ∈ (adjGraph src tgt).edgeFinset,
      (conductance src tgt ℓ z)⁻¹ ≤ ∑ e ∈ Finset.univ.filter (fun e => s(src e, tgt e) = z), ℓ e := by
    intro z hz
    induction z using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hz
      obtain ⟨-, e₀, he₀⟩ := hz
      have hmem : e₀ ∈ Finset.univ.filter (fun e => s(src e, tgt e) = s(a, b)) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rcases he₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]
        · rw [h1, h2, Sym2.eq_swap]
      calc (conductance src tgt ℓ s(a, b))⁻¹ ≤ ((ℓ e₀)⁻¹)⁻¹ := by
            refine inv_anti₀ (inv_pos.mpr (hℓ e₀)) ?_
            exact Finset.single_le_sum (f := fun e => (ℓ e)⁻¹) (fun e _ => (inv_pos.mpr (hℓ e)).le) hmem
        _ = ℓ e₀ := inv_inv _
        _ ≤ ∑ e ∈ Finset.univ.filter (fun e => s(src e, tgt e) = s(a, b)), ℓ e :=
            Finset.single_le_sum (f := ℓ) (fun e _ => (hℓ e).le) hmem
  calc ∑ z ∈ (adjGraph src tgt).edgeFinset, (conductance src tgt ℓ z)⁻¹
      ≤ ∑ z ∈ (adjGraph src tgt).edgeFinset,
          ∑ e ∈ Finset.univ.filter (fun e => s(src e, tgt e) = z), ℓ e := Finset.sum_le_sum key
    _ ≤ ∑ z, ∑ e ∈ Finset.univ.filter (fun e => s(src e, tgt e) = z), ℓ e :=
        Finset.sum_le_univ_sum_of_nonneg fun z => Finset.sum_nonneg fun e _ => (hℓ e).le
    _ = ∑ e, ℓ e := Finset.sum_fiberwise Finset.univ (fun e => s(src e, tgt e)) ℓ

private def IsGrounded (v₀ : V) (b g : V → ℝ) : Prop :=
  g v₀ = 0 ∧ ∀ v, v ≠ v₀ →
    ∑ u ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u) * (g v - g u) = b v

open Classical in

private def groundPotential (v₀ : V) (v u : V) : ℝ :=
  if h : ∃ g : V → ℝ, IsGrounded src tgt ℓ v₀ (Pi.single u 1) g then h.choose v else 0

private theorem groundPotential_ground (v₀ u : V) : groundPotential src tgt ℓ v₀ v₀ u = 0 := by
  unfold groundPotential
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

variable {src tgt ℓ}

private theorem IsGrounded.unique (hconn : (adjGraph src tgt).Connected) (hℓ : ∀ e, 0 < ℓ e) {v₀ : V}
    {b g g' : V → ℝ} (hg : IsGrounded src tgt ℓ v₀ b g) (hg' : IsGrounded src tgt ℓ v₀ b g') :
    g = g' :=
  (SimpleGraph.existsUnique_grounded (adjGraph src tgt) hconn (conductance src tgt ℓ)
    (fun _ hz => conductance_pos src tgt ℓ hℓ hz) v₀ b).unique hg hg'

private theorem IsGrounded.add {v₀ : V} {b g b' g' : V → ℝ} (hg : IsGrounded src tgt ℓ v₀ b g)
    (hg' : IsGrounded src tgt ℓ v₀ b' g') : IsGrounded src tgt ℓ v₀ (b + b') (g + g') := by
  refine ⟨?_, fun v hv => ?_⟩
  · show g v₀ + g' v₀ = 0
    rw [hg.1, hg'.1, add_zero]
  simp only [Pi.add_apply]
  rw [← hg.2 v hv, ← hg'.2 v hv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  ring

variable (src tgt ℓ)

private theorem isGrounded_groundPotential (hconn : (adjGraph src tgt).Connected) (hℓ : ∀ e, 0 < ℓ e)
    (v₀ u : V) :
    IsGrounded src tgt ℓ v₀ (Pi.single u 1) (fun v => groundPotential src tgt ℓ v₀ v u) := by
  have hex : ∃ g : V → ℝ, IsGrounded src tgt ℓ v₀ (Pi.single u 1) g :=
    (SimpleGraph.existsUnique_grounded (adjGraph src tgt) hconn (conductance src tgt ℓ)
      (fun _ hz => conductance_pos src tgt ℓ hℓ hz) v₀ (Pi.single u 1)).exists
  have hfun : (fun v => groundPotential src tgt ℓ v₀ v u) = hex.choose := by
    funext v
    unfold groundPotential
    rw [dif_pos hex]
  rw [hfun]
  exact hex.choose_spec

private theorem isGrounded_sum_mul_groundPotential (hconn : (adjGraph src tgt).Connected)
    (hℓ : ∀ e, 0 < ℓ e) (v₀ : V) (B : V → ℝ) :
    IsGrounded src tgt ℓ v₀ B (fun v => ∑ u, B u * groundPotential src tgt ℓ v₀ v u) := by
  refine ⟨?_, fun v hv => ?_⟩
  · show ∑ u, B u * groundPotential src tgt ℓ v₀ v₀ u = 0
    exact Finset.sum_eq_zero fun u _ => by rw [groundPotential_ground, mul_zero]
  have h : ∀ u, ∑ u' ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u') *
      (groundPotential src tgt ℓ v₀ v u - groundPotential src tgt ℓ v₀ u' u)
        = (Pi.single u (1 : ℝ) : V → ℝ) v :=
    fun u => (isGrounded_groundPotential src tgt ℓ hconn hℓ v₀ u).2 v hv
  show ∑ u' ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u') *
      ((∑ u, B u * groundPotential src tgt ℓ v₀ v u) - ∑ u, B u * groundPotential src tgt ℓ v₀ u' u)
    = B v
  calc ∑ u' ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u') *
          ((∑ u, B u * groundPotential src tgt ℓ v₀ v u) -
            ∑ u, B u * groundPotential src tgt ℓ v₀ u' u)
      = ∑ u' ∈ (adjGraph src tgt).neighborFinset v, ∑ u, B u * (conductance src tgt ℓ s(v, u') *
          (groundPotential src tgt ℓ v₀ v u - groundPotential src tgt ℓ v₀ u' u)) := by
        refine Finset.sum_congr rfl fun u' _ => ?_
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ = ∑ u, B u * ∑ u' ∈ (adjGraph src tgt).neighborFinset v, conductance src tgt ℓ s(v, u') *
          (groundPotential src tgt ℓ v₀ v u - groundPotential src tgt ℓ v₀ u' u) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ u, B u * (Pi.single u (1 : ℝ) : V → ℝ) v := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [h u]
    _ = B v := by
        rw [Finset.sum_eq_single v]
        · rw [Pi.single_eq_same, mul_one]
        · intro u _ hu
          rw [Pi.single_eq_of_ne' hu, mul_zero]
        · intro hv'
          exact absurd (Finset.mem_univ v) hv'

private theorem abs_groundPotential_le (hconn : (adjGraph src tgt).Connected) (hℓ : ∀ e, 0 < ℓ e)
    (v₀ v u : V) : |groundPotential src tgt ℓ v₀ v u| ≤ ∑ e, ℓ e := by
  have hg := isGrounded_groundPotential src tgt ℓ hconn hℓ v₀ u
  have h := SimpleGraph.abs_apply_le_of_grounded (adjGraph src tgt) hconn (conductance src tgt ℓ)
    (fun _ hz => conductance_pos src tgt ℓ hℓ hz) v₀ (Pi.single u 1)
    (fun v => groundPotential src tgt ℓ v₀ v u) hg.1 hg.2 v
  have hB : ∑ u' ∈ Finset.univ.erase v₀, |(Pi.single u (1 : ℝ) : V → ℝ) u'| ≤ 1 := by
    calc ∑ u' ∈ Finset.univ.erase v₀, |(Pi.single u (1 : ℝ) : V → ℝ) u'|
        ≤ ∑ u', |(Pi.single u (1 : ℝ) : V → ℝ) u'| :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => abs_nonneg _
      _ = 1 := by
          rw [Finset.sum_eq_single u]
          · rw [Pi.single_eq_same, abs_one]
          · intro u' _ hu'
            rw [Pi.single_eq_of_ne hu', abs_zero]
          · intro hu
            exact absurd (Finset.mem_univ u) hu
  have hR0 : 0 ≤ ∑ z ∈ (adjGraph src tgt).edgeFinset, (conductance src tgt ℓ z)⁻¹ :=
    Finset.sum_nonneg fun z hz => (inv_pos.mpr (conductance_pos src tgt ℓ hℓ hz)).le
  calc |groundPotential src tgt ℓ v₀ v u|
      ≤ (∑ z ∈ (adjGraph src tgt).edgeFinset, (conductance src tgt ℓ z)⁻¹) *
          ∑ u' ∈ Finset.univ.erase v₀, |(Pi.single u (1 : ℝ) : V → ℝ) u'| := h
    _ ≤ (∑ e, ℓ e) * 1 :=
        mul_le_mul (sum_inv_conductance_le src tgt ℓ hℓ) hB
          (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun e _ => (hℓ e).le)
    _ = ∑ e, ℓ e := mul_one _

end Ground
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph"

end ReductionGraph
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

section Glue

open ReductionGraph

variable {X : Type*} {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
  (src tgt : E → V) (ℓ : E → ℝ) (J : V → V → ℝ) (ρ : X → V ⊕ (E × ℝ)) (knear : X → X → ℝ)

private def gluedKernel (P Q : X) : ℝ :=
  if piece (ρ P) = piece (ρ Q) then knear P Q else pairPotential src tgt ℓ J (ρ P) (ρ Q)

private theorem gluedKernel_of_piece_ne {P Q : X} (h : piece (ρ P) ≠ piece (ρ Q)) :
    gluedKernel src tgt ℓ J ρ knear P Q = pairPotential src tgt ℓ J (ρ P) (ρ Q) := if_neg h

private theorem _root_.AlgebraicCurve.abs_gluedKernel_sub_prox_le {L : Type*} [Mul L] [Sub L] (ν : L → ℝ) {ι : Type*}
    (x : X → ι → L) {R CΓ Cfar lam : ℝ} (hJ : ∀ v u, |J v u| ≤ R) (hR : R ≤ CΓ * lam) {P Q : X}
    (hP : OnSkeleton ℓ (ρ P)) (hQ : OnSkeleton ℓ (ρ Q)) (hPQ : piece (ρ P) ≠ piece (ρ Q))
    (hfar : |prox ν (x P) (x Q)| ≤ Cfar * lam) :
    |gluedKernel src tgt ℓ J ρ knear P Q - prox ν (x P) (x Q)| ≤ (CΓ + Cfar) * lam := by
  rw [gluedKernel_of_piece_ne src tgt ℓ J ρ knear hPQ]
  have h1 := abs_pairPotential_le src tgt ℓ J hJ hP hQ
  calc |pairPotential src tgt ℓ J (ρ P) (ρ Q) - prox ν (x P) (x Q)|
      ≤ |pairPotential src tgt ℓ J (ρ P) (ρ Q)| + |prox ν (x P) (x Q)| := abs_sub _ _
    _ ≤ R + Cfar * lam := add_le_add h1 hfar
    _ ≤ (CΓ + Cfar) * lam := by rw [add_mul]; exact add_le_add hR le_rfl

p2m_export "AlgebraicCurve" "abs_gluedKernel_sub_prox_le"
end Glue
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

section Retraction

open ReductionGraph

variable {X : Type*} {V E : Type*} (cd : V → Set X) (ad : E → Set X) (pos : E → X → ℝ)

open Classical in

private def retraction (hcov : ∀ P, (∃ i, P ∈ cd i) ∨ ∃ e, P ∈ ad e) (P : X) : V ⊕ (E × ℝ) :=
  if h : ∃ i, P ∈ cd i then Sum.inl h.choose
  else Sum.inr (((hcov P).resolve_left h).choose, pos ((hcov P).resolve_left h).choose P)

variable (hcov : ∀ P, (∃ i, P ∈ cd i) ∨ ∃ e, P ∈ ad e)

private theorem retraction_eq_inl {P : X} {i : V} (hP : P ∈ cd i) (huniq : ∀ j, P ∈ cd j → j = i) :
    retraction cd ad pos hcov P = Sum.inl i := by
  have h : ∃ i, P ∈ cd i := ⟨i, hP⟩
  unfold retraction
  rw [dif_pos h, huniq _ h.choose_spec]

private theorem retraction_eq_inr {P : X} {e : E} (huniq : ∀ e', P ∈ ad e' → e' = e)
    (hnot : ∀ i, P ∉ cd i) : retraction cd ad pos hcov P = Sum.inr (e, pos e P) := by
  have h : ¬ ∃ i, P ∈ cd i := fun ⟨i, hi⟩ => hnot i hi
  unfold retraction
  rw [dif_neg h, huniq _ ((hcov P).resolve_left h).choose_spec]

private theorem onSkeleton_retraction (ℓ : E → ℝ) (hpos : ∀ e, ∀ P ∈ ad e, 0 ≤ pos e P ∧ pos e P ≤ ℓ e)
    (P : X) : OnSkeleton ℓ (retraction cd ad pos hcov P) := by
  unfold retraction
  split_ifs with h
  · trivial
  · exact hpos _ _ ((hcov P).resolve_left h).choose_spec

private theorem piece_retraction_ne {P Q : X}
    (huc : ∀ R, ∀ i j, R ∈ cd i → R ∈ cd j → j = i) (hua : ∀ R, ∀ e e', R ∈ ad e → R ∈ ad e' → e' = e)
    (hca : ∀ R, ∀ i e, R ∈ cd i → R ∉ ad e)
    (hPQ : (∃ i, P ∈ cd i ∧ Q ∉ cd i) ∨ ∃ e, P ∈ ad e ∧ Q ∉ ad e) :
    piece (retraction cd ad pos hcov P) ≠ piece (retraction cd ad pos hcov Q) := by
  intro heq
  rcases hPQ with ⟨i, hPi, hQi⟩ | ⟨e, hPe, hQe⟩
  · rw [retraction_eq_inl cd ad pos hcov hPi (fun j hj => huc P i j hPi hj), piece_inl] at heq
    rcases hcov Q with ⟨i', hQi'⟩ | ⟨e', hQe'⟩
    · rw [retraction_eq_inl cd ad pos hcov hQi' (fun j hj => huc Q i' j hQi' hj), piece_inl] at heq
      have hii' : i = i' := Sum.inl_injective heq
      exact hQi (hii' ▸ hQi')
    · rw [retraction_eq_inr cd ad pos hcov (fun e'' he'' => hua Q e' e'' hQe' he'')
        (fun i'' hi'' => hca Q i'' e' hi'' hQe'), piece_inr] at heq
      exact Sum.inl_ne_inr heq
  · have hPnot : ∀ i, P ∉ cd i := fun i hi => hca P i e hi hPe
    rw [retraction_eq_inr cd ad pos hcov (fun e'' he'' => hua P e e'' hPe he'') hPnot, piece_inr] at heq
    rcases hcov Q with ⟨i', hQi'⟩ | ⟨e', hQe'⟩
    · rw [retraction_eq_inl cd ad pos hcov hQi' (fun j hj => huc Q i' j hQi' hj), piece_inl] at heq
      exact Sum.inr_ne_inl heq
    · rw [retraction_eq_inr cd ad pos hcov (fun e'' he'' => hua Q e' e'' hQe' he'')
        (fun i'' hi'' => hca Q i'' e' hi'' hQe'), piece_inr] at heq
      have hee' : e = e' := Sum.inr_injective heq
      exact hQe (hee' ▸ hQe')

end Retraction
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_param_sub"
p2m_open "AlgebraicCurve.Annulus"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

private theorem abv_modulus_lt_one (An : Annulus A F) (μ : AbsoluteValue L ℝ)
    (hμ : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (hmod : (An.modulus : L) ≠ 0) : μ (An.modulus : L) < 1 := by
  have hle : μ (An.modulus : L) ≤ 1 := (hμ _).mp An.modulus.2
  refine lt_of_le_of_ne hle fun heq => ?_
  have hinv : (An.modulus : L)⁻¹ ∈ A := (hμ _).mpr (by rw [map_inv₀, heq, inv_one])
  have hunit : IsUnit An.modulus :=
    IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hmod))
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp An.modulus_mem)) hunit

private theorem neg_log_abv_modulus_pos (An : Annulus A F) (μ : AbsoluteValue L ℝ)
    (hμ : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (hmod : (An.modulus : L) ≠ 0) :
    0 < -Real.log (μ (An.modulus : L)) :=
  neg_pos.mpr (Real.log_neg (μ.pos hmod) (abv_modulus_lt_one An μ hμ hmod))

private theorem neg_log_abv_evalAt_param_mem (An : Annulus A F) (μ : AbsoluteValue L ℝ)
    (hμ : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (hmod : (An.modulus : L) ≠ 0) {P : Place L F} (hP : P ∈ An.dom) :
    0 ≤ -Real.log (μ (P.evalAt An.param)) ∧
      -Real.log (μ (P.evalAt An.param)) ≤ -Real.log (μ (An.modulus : L)) := by
  obtain ⟨-, -, ⟨hzA, -⟩, hz0, m, -, hmod_eq⟩ := An.mem_dom P hP
  have hz1 : μ (P.evalAt An.param) ≤ 1 := (hμ _).mp hzA
  have hzpos : 0 < μ (P.evalAt An.param) := μ.pos hz0
  have hm1 : μ (m : L) ≤ 1 := (hμ _).mp m.2
  have hmodle : μ (An.modulus : L) ≤ μ (P.evalAt An.param) := by
    rw [hmod_eq, map_mul]
    exact mul_le_of_le_one_right hzpos.le hm1
  refine ⟨neg_nonneg.mpr (Real.log_nonpos hzpos.le hz1), neg_le_neg ?_⟩
  exact Real.log_le_log (μ.pos hmod) hmodle

end Annulus
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace AdaptedCovering

open IsLocalRing ReductionGraph

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}
  (Γ : AdaptedCovering pf A F P₀ p s μ)

private theorem covers (P : Place (AlgebraicClosure ℚ) F) :
    (∃ i, P ∈ (Γ.chart i).dom) ∨ ∃ e, P ∈ (Γ.an e).dom := by
  rcases Γ.partition P with ⟨i, hi, -, -⟩ | ⟨e, he, -, -⟩
  exacts [Or.inl ⟨i, hi⟩, Or.inr ⟨e, he⟩]

private theorem chart_unique (P : Place (AlgebraicClosure ℚ) F) (i j : Fin pf.n)
    (hi : P ∈ (Γ.chart i).dom) (hj : P ∈ (Γ.chart j).dom) : j = i := by
  rcases Γ.partition P with ⟨i', -, huniq, -⟩ | ⟨-, -, -, hexcl⟩
  · exact (huniq j hj).trans (huniq i hi).symm
  · exact absurd hi (hexcl i)

private theorem an_unique (P : Place (AlgebraicClosure ℚ) F) (e e' : Fin pf.m)
    (he : P ∈ (Γ.an e).dom) (he' : P ∈ (Γ.an e').dom) : e' = e := by
  rcases Γ.partition P with ⟨-, -, -, hexcl⟩ | ⟨e'', -, huniq, -⟩
  · exact absurd he (hexcl e)
  · exact (huniq e' he').trans (huniq e he).symm

private theorem chart_an_disjoint (P : Place (AlgebraicClosure ℚ) F) (i : Fin pf.n) (e : Fin pf.m)
    (hi : P ∈ (Γ.chart i).dom) : P ∉ (Γ.an e).dom := by
  rcases Γ.partition P with ⟨-, -, -, hexcl⟩ | ⟨-, -, -, hexcl⟩
  · exact hexcl e
  · exact absurd hi (hexcl i)

private theorem connected_adjGraph : (adjGraph Γ.src Γ.tgt).Connected := by
  haveI : Nonempty (Fin pf.n) := ⟨Γ.cuspIdx⟩
  refine ⟨fun a b => ?_⟩
  have h := Γ.conn a b
  induction h with
  | refl => exact SimpleGraph.Reachable.refl a
  | tail _ hstep ih =>
    rename_i c b' _
    rcases eq_or_ne c b' with rfl | hne
    · exact ih
    · exact ih.trans (SimpleGraph.Adj.reachable ⟨hne, hstep⟩)

private theorem len_pos (e : Fin pf.m) : 0 < Γ.len e :=
  Annulus.neg_log_abv_modulus_pos (Γ.an e) μ Γ.ball (Γ.pair e).2.2.1

private theorem len_le (hp : μ p ≠ 0) (e : Fin pf.m) : Γ.len e ≤ (pf.k : ℝ) * (-Real.log (μ p)) := by
  obtain ⟨a, haA, heq⟩ := Γ.thick e
  have hmod : ((Γ.an e).modulus : AlgebraicClosure ℚ) ≠ 0 := (Γ.pair e).2.2.1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at heq
    have hμ : μ p ^ pf.k = 0 := by rw [← map_pow, heq, map_zero]
    exact pow_ne_zero pf.k hp hμ
  have hμmod : μ p ^ pf.k ≤ μ ((Γ.an e).modulus : AlgebraicClosure ℚ) := by
    have h := congrArg μ heq
    rw [map_pow, map_mul] at h
    calc μ p ^ pf.k = μ ((Γ.an e).modulus : AlgebraicClosure ℚ) * μ a := h
      _ ≤ μ ((Γ.an e).modulus : AlgebraicClosure ℚ) * 1 :=
          mul_le_mul_of_nonneg_left ((Γ.ball a).mp haA) (μ.nonneg _)
      _ = μ ((Γ.an e).modulus : AlgebraicClosure ℚ) := mul_one _
  unfold len
  rw [mul_neg, ← Real.log_pow]
  exact neg_le_neg (Real.log_le_log (pow_pos (lt_of_le_of_ne (μ.nonneg p) (Ne.symm hp)) pf.k) hμmod)

private theorem sum_len_le (hp : μ p ≠ 0) :
    ∑ e, Γ.len e ≤ ((pf.m : ℝ) * (pf.k : ℝ)) * (-Real.log (μ p)) := by
  calc ∑ e, Γ.len e ≤ ∑ _e : Fin pf.m, (pf.k : ℝ) * (-Real.log (μ p)) :=
        Finset.sum_le_sum fun e _ => Γ.len_le hp e
    _ = ((pf.m : ℝ) * (pf.k : ℝ)) * (-Real.log (μ p)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

private def retract (P : Place (AlgebraicClosure ℚ) F) : Fin pf.n ⊕ (Fin pf.m × ℝ) :=
  AlgebraicCurve.retraction (fun i => (Γ.chart i).dom) (fun e => (Γ.an e).dom)
    (fun e P => -Real.log (μ (P.evalAt (Γ.an e).param))) Γ.covers P

private theorem onSkeleton_retract (P : Place (AlgebraicClosure ℚ) F) :
    OnSkeleton Γ.len (Γ.retract P) :=
  AlgebraicCurve.onSkeleton_retraction (fun i => (Γ.chart i).dom) (fun e => (Γ.an e).dom)
    (fun e Q => -Real.log (μ (Q.evalAt (Γ.an e).param))) Γ.covers Γ.len
    (fun e _ hQ => Annulus.neg_log_abv_evalAt_param_mem (Γ.an e) μ Γ.ball (Γ.pair e).2.2.1 hQ) P

private theorem far_of_mem_notMem {P Q : Place (AlgebraicClosure ℚ) F}
    (h : (∃ i, P ∈ (Γ.chart i).dom ∧ Q ∉ (Γ.chart i).dom) ∨
         (∃ e, P ∈ (Γ.an e).dom ∧ Q ∉ (Γ.an e).dom)) :
    |prox μ (evalVec s P) (evalVec s Q)| ≤ pf.Cc * (-Real.log (μ p)) := by
  refine Γ.far P Q ?_ ?_
  · intro i hPi hQi
    rcases h with ⟨i', hPi', hQi'⟩ | ⟨e, hPe, -⟩
    · exact hQi' (Γ.chart_unique P i' i hPi' hPi ▸ hQi)
    · exact Γ.chart_an_disjoint P i e hPi hPe
  · intro e hPe hQe
    rcases h with ⟨i, hPi, -⟩ | ⟨e', hPe', hQe'⟩
    · exact Γ.chart_an_disjoint P i e hPi hPe
    · exact hQe' (Γ.an_unique P e' e hPe' hPe ▸ hQe)

private theorem abs_gluedKernel_sub_prox_le (hp : μ p ≠ 0) (knear : Place (AlgebraicClosure ℚ) F →
    Place (AlgebraicClosure ℚ) F → ℝ) {P Q : Place (AlgebraicClosure ℚ) F}
    (hPQ : (∃ i, P ∈ (Γ.chart i).dom ∧ Q ∉ (Γ.chart i).dom) ∨
           (∃ e, P ∈ (Γ.an e).dom ∧ Q ∉ (Γ.an e).dom)) :
    |AlgebraicCurve.gluedKernel Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx)
        Γ.retract knear P Q - prox μ (evalVec s P) (evalVec s Q)|
      ≤ ((pf.m : ℝ) * (pf.k : ℝ) + pf.Cc) * (-Real.log (μ p)) :=
  AlgebraicCurve.abs_gluedKernel_sub_prox_le Γ.src Γ.tgt Γ.len
    (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx) Γ.retract knear
    (μ : AlgebraicClosure ℚ → ℝ) (fun P => evalVec s P) (R := ∑ e, Γ.len e)
    (abs_groundPotential_le Γ.src Γ.tgt Γ.len Γ.connected_adjGraph Γ.len_pos Γ.cuspIdx)
    (Γ.sum_len_le hp) (Γ.onSkeleton_retract P) (Γ.onSkeleton_retract Q)
    (AlgebraicCurve.piece_retraction_ne (fun i => (Γ.chart i).dom) (fun e => (Γ.an e).dom)
      (fun e P => -Real.log (μ (P.evalAt (Γ.an e).param))) Γ.covers
      Γ.chart_unique Γ.an_unique Γ.chart_an_disjoint hPQ)
    (Γ.far_of_mem_notMem hPQ)

end AdaptedCovering
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
namespace AdaptedCovering
p2m_open "AlgebraicCurve"

open IsLocalRing

private theorem exists_profile_forall_nonempty (F : Type) [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (P₀ : Place (AlgebraicClosure ℚ) F) (p : ℕ) {r : ℕ} (s : Fin r → F)
    (h :
    ∃ (n m B k : ℕ) (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A F (Fbar i))
      (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → F),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) F ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) F,
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, P₀ ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ e, ∀ P ∈ (An e).dom, ∀ Q ∈ (An e).dom, P ≠ Q →
          (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (An e).param - Q.evalAt (An e).param))|
            ≤ Cc * (-Real.log (μ ((An e).modulus : AlgebraicClosure ℚ)))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) F,
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) :
    ∃ pf : CoveringProfile, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
          Nonempty (AdaptedCovering pf A F P₀ (p : AlgebraicClosure ℚ) s μ) := by
  obtain ⟨n, m, B, k, Cc, hcov⟩ := h
  refine ⟨⟨n, m, B, k, Cc⟩, fun A hAp μ hμ hball => ?_⟩
  obtain ⟨Fbar, instF, instA, C, An, An', src, tgt, xs, xt, T, hpair, hatt, hnode, hendu, hpart,
    ⟨i₀, hcusp, hbasis⟩, hres, hconn, hthick, hdisc, hanc, hchart, hfar⟩ := hcov A hAp
  exact ⟨
    { Fbar := Fbar
      instField := instF
      instAlg := instA
      chart := C
      an := An
      an' := An'
      src := src
      tgt := tgt
      xs := xs
      xt := xt
      T := T
      cuspIdx := i₀
      hna := hμ
      ball := hball
      pair := by exact hpair
      attached := by exact hatt
      node_end := by exact hnode
      end_unique := by exact hendu
      partition := by exact hpart
      cusp_mem := by exact hcusp
      basis_norm := by exact hbasis
      res := by exact hres
      conn := by exact hconn
      thick := by exact hthick
      disc := by exact hdisc
      anCmp := by exact hanc μ hμ hball
      chartCmp := by exact hchart μ hμ hball
      far := by exact hfar μ hμ hball }⟩

end AlgebraicCurve.AdaptedCovering
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.ModularCurve IsLocalRing"

namespace ModularCurve p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis cuspInftyBar qExpand jq divisorExpansions modularFunctionFieldFull modularFunctionFieldBar coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange exists_uniform_dualGraphCovering_of_prime_of_five_le hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar coeffMap_jqModC divisorExpansionsC modularFunctionFieldFullC jqModC coeffMap_qExpand ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.exists_profile_forall_nonempty_adaptedCovering (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (p : ℕ)

    (h :
    ∃ (n m B k : ℕ) (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar N) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar N)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar N),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar N ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ e, ∀ P ∈ (An e).dom, ∀ Q ∈ (An e).dom, P ≠ Q →
          (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (An e).param - Q.evalAt (An e).param))|
            ≤ Cc * (-Real.log (μ ((An e).modulus : AlgebraicClosure ℚ)))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))))

    : ∃ pf : CoveringProfile, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
          (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
            Nonempty (AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
              (p : AlgebraicClosure ℚ) s μ) :=
  AdaptedCovering.exists_profile_forall_nonempty (modularFunctionFieldBar N) (cuspInftyBar N) p s h

p2m_open_scoped "ModularCurve" in
open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve in

private theorem ModularCurve.exists_profile_forall_nonempty_adaptedCovering_of_isEmbBasis
    (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (p : ℕ) (hp : p.Prime) :
    ∃ pf : CoveringProfile, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
        ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean ⇑μ →
          (∀ y, y ∈ A ↔ μ y ≤ 1) →
            Nonempty (AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
              (p : AlgebraicClosure ℚ) s μ) :=
  ModularCurve.exists_profile_forall_nonempty_adaptedCovering N s p
    (ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le N hN hN5 s hs p hp)

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace OfTopTransport

private theorem deg_eq_one_of_isRational {K F : Type*} [Field K] [Field F] [Algebra K F] (y : Place K F)
    (hy : y.IsRational) : y.deg = 1 := by
  have hinj : Function.Injective (algebraMap K y.ResidueField) :=
    (algebraMap K y.ResidueField).injective
  have hbij : Function.Bijective (Algebra.ofId K y.ResidueField) := ⟨hinj, hy⟩
  unfold Place.deg
  rw [← (AlgEquiv.ofBijective (Algebra.ofId K y.ResidueField) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

private theorem isRational_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra K v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra K v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

end OfTopTransport
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv ord_zpow algebraMap_mem' toValuationSubring IsRational residueInv_algebraMap evalAt evalAt_of_mem evalAt_one"
p2m_open "AlgebraicCurve.Place~exists_ord_eq_one~evalAt_mul_of_mem~evalAt_ne_zero_of_ord_eq_zero~deg_eq_one_of_isRational~residue_algebraMap"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_finset_prod {ι : Type*} (S : Finset ι) (g : ι → F) (hg : ∀ i ∈ S, g i ≠ 0) :
    v.ord (∏ i ∈ S, g i) = ∑ i ∈ S, v.ord (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hg a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

p2m_export "AlgebraicCurve.Place" "ord_finset_prod"

private theorem _root_.AlgebraicCurve.Place.evalAt_finset_prod_of_mem {ι : Type*} (hv : v.IsRational) (S : Finset ι) (g : ι → F)
    (hg : ∀ i ∈ S, g i ∈ v.toValuationSubring) :
    v.evalAt (∏ i ∈ S, g i) = ∏ i ∈ S, v.evalAt (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [v.evalAt_one]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      GaussReduction.evalAt_mul_of_mem v hv (hg a (Finset.mem_insert_self _ _))
        (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

p2m_export "AlgebraicCurve.Place" "evalAt_finset_prod_of_mem"

private theorem _root_.AlgebraicCurve.Place.evalAt_zpow_of_ord_eq_zero (hv : v.IsRational) {f : F} (hf : f ≠ 0) (h : v.ord f = 0)
    (n : ℤ) : v.evalAt (f ^ n) = v.evalAt f ^ n := by
  have hmem : f ∈ v.toValuationSubring := GaussReduction.mem_of_ord_nonneg_gen v hf h.ge
  have hpow : ∀ m : ℕ, v.evalAt (f ^ m) = v.evalAt f ^ m := by
    intro m
    induction m with
    | zero => simp [v.evalAt_one]
    | succ m ih =>
      rw [pow_succ, GaussReduction.evalAt_mul_of_mem v hv (pow_mem hmem m) hmem, ih, pow_succ]
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc, zpow_negSucc, ← hpow (m + 1)]
    refine StandardAnnulus.evalAt_inv_of_ord_eq_zero v hv (pow_ne_zero _ hf) ?_
    have : (f ^ (m + 1) : F) = f ^ ((m + 1 : ℕ) : ℤ) := by rw [zpow_natCast]
    rw [this, v.ord_zpow, h, mul_zero]

p2m_export "AlgebraicCurve.Place" "evalAt_zpow_of_ord_eq_zero"
end Place
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

private theorem abv_coe_eq_one_of_isUnit {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) {a : A} (ha : IsUnit a) :
    μ (a : L) = 1 := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  have hab : μ (a : L) * μ (b : L) = 1 := by
    have h := congrArg Subtype.val hb
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    rw [← map_mul, h, map_one]
  have ha1 : μ (a : L) ≤ 1 := (hA _).mp a.2
  have hb1 : μ (b : L) ≤ 1 := (hA _).mp b.2
  refine le_antisymm ha1 ?_
  have h3 : μ (a : L) * μ (b : L) ≤ μ (a : L) * 1 := mul_le_mul_of_nonneg_left hb1 (μ.nonneg _)
  rw [hab, mul_one] at h3
  exact h3

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff placeMap residue nodes exists_smul_mem pointwise residue_algebraMap ker_residue mapDomain_placeMap placeMap_not_mem_nodes dom"
p2m_open "AlgebraicCurve.ComponentChart"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (C : ComponentChart A F Fbar)

private theorem _root_.AlgebraicCurve.ComponentChart.zpow_mem_of_residue_ne_zero {u : F} (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0)
    (n : ℤ) : ∃ h : u ^ n ∈ C.integers, C.residue ⟨u ^ n, h⟩ ≠ 0 := by
  have hpow : ∀ m : ℕ, ∃ h : u ^ m ∈ C.integers, C.residue ⟨u ^ m, h⟩ ≠ 0 := by
    intro m
    refine ⟨pow_mem hu m, ?_⟩
    have hsub : (⟨u ^ m, pow_mem hu m⟩ : C.integers) = (⟨u, hu⟩ : C.integers) ^ m :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow])
    rw [hsub, map_pow]
    exact pow_ne_zero m hres
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact hpow m
  · rw [zpow_negSucc]
    obtain ⟨hm, hresm⟩ := hpow (m + 1)
    exact C.exists_inv_mem_residue_ne_zero (u := ⟨u ^ (m + 1), hm⟩) hresm

p2m_export "AlgebraicCurve.ComponentChart" "zpow_mem_of_residue_ne_zero"

private theorem _root_.AlgebraicCurve.ComponentChart.prod_mem_of_residue_ne_zero {ι : Type*} (S : Finset ι) (g : ι → F)
    (hg : ∀ i ∈ S, ∃ h : g i ∈ C.integers, C.residue ⟨g i, h⟩ ≠ 0) :
    ∃ h : (∏ i ∈ S, g i) ∈ C.integers, C.residue ⟨∏ i ∈ S, g i, h⟩ ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h1 : (∏ i ∈ (∅ : Finset ι), g i) ∈ C.integers := by
      rw [Finset.prod_empty]
      exact one_mem _
    refine ⟨h1, ?_⟩
    have hsub : (⟨∏ i ∈ (∅ : Finset ι), g i, h1⟩ : C.integers) = 1 := Subtype.ext (show (∏ i ∈ (∅ : Finset ι), g i) = ((1 : C.integers) : F) by
        rw [Finset.prod_empty]; rfl)
    rw [hsub, map_one]
    exact one_ne_zero
  | insert a S ha ih =>
    obtain ⟨ha1, ha2⟩ := hg a (Finset.mem_insert_self a S)
    obtain ⟨hS1, hS2⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hmem : (∏ i ∈ insert a S, g i) ∈ C.integers := by
      rw [Finset.prod_insert ha]
      exact mul_mem ha1 hS1
    refine ⟨hmem, ?_⟩
    have hsub : (⟨∏ i ∈ insert a S, g i, hmem⟩ : C.integers) = ⟨g a, ha1⟩ * ⟨∏ i ∈ S, g i, hS1⟩ :=
      Subtype.ext (Finset.prod_insert ha)
    rw [hsub, map_mul]
    exact mul_ne_zero ha2 hS2

p2m_export "AlgebraicCurve.ComponentChart" "prod_mem_of_residue_ne_zero"

open Classical in

private theorem _root_.AlgebraicCurve.ComponentChart.ord_residue_eq_sum_fibre {g : F} (hg : g ∈ C.integers) (hres : C.residue ⟨g, hg⟩ ≠ 0)
    {P : Place L F} (hP : P ∈ C.dom) (D : Divisor L F) (hD : ∀ w, D w = w.ord g) :
    (C.placeMap P).ord (C.residue ⟨g, hg⟩)
      = ∑ w ∈ D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P), D w := by
  set D' := D.filter (fun w => w ∈ C.dom) with hD'
  have h1 : ∀ w ∈ C.dom, D' w = w.ord ((⟨g, hg⟩ : C.integers) : F) := fun w hw => by
    rw [hD', Finsupp.filter_apply_pos _ _ hw]
    exact hD w
  have h2 : ∀ w, w ∉ C.dom → D' w = 0 := fun w hw => by
    rw [hD', Finsupp.filter_apply_neg _ _ hw]
  have hmd := C.mapDomain_placeMap ⟨g, hg⟩ hres D' h1 h2 (C.placeMap P)
    (C.placeMap_not_mem_nodes P hP)
  rw [← hmd]
  have hsupp : D'.support.filter (fun a => C.placeMap a = C.placeMap P)
      = D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P) := by
    rw [hD', Finsupp.support_filter, Finset.filter_filter]
  simp only [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply]
  rw [Finsupp.sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, hsupp]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [hD', Finsupp.filter_apply_pos _ _ hw.2.1]

p2m_export "AlgebraicCurve.ComponentChart" "ord_residue_eq_sum_fibre"

private theorem _root_.AlgebraicCurve.ComponentChart.ord_eq_one_of_disc [HasPrincipalDivisors L F] {w : Place L F} (hw : w ∈ C.dom) {u : F}
    (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0)
    (hord1 : (C.placeMap w).ord (C.residue ⟨u, hu⟩) = 1) (hpos : 0 < w.ord u)
    (hsep : ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap w → Q ≠ w → Q.ord u = 0) :
    w.ord u = 1 := by
  classical
  have hu0 : u ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hres
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) u hu0
  have hsum := C.ord_residue_eq_sum_fibre hu hres hw D hD
  rw [hord1] at hsum
  have hS : D.support.filter (fun Q => Q ∈ C.dom ∧ C.placeMap Q = C.placeMap w) = {w} := by
    ext Q
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hDQ, hQdom, hQmap⟩
      by_contra hne
      exact hDQ (by rw [hD Q]; exact hsep Q hQdom hQmap hne)
    · rintro rfl
      exact ⟨by rw [hD]; exact ne_of_gt hpos, hw, rfl⟩
  rw [hS, Finset.sum_singleton, hD w] at hsum
  exact hsum.symm

p2m_export "AlgebraicCurve.ComponentChart" "ord_eq_one_of_disc"

private theorem _root_.AlgebraicCurve.ComponentChart.abv_evalAt_eq_one (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {P : Place L F} (hP : P ∈ C.dom) (hPrat : P.IsRational) {g : F} (hg : g ∈ C.integers)
    (hres : C.residue ⟨g, hg⟩ ≠ 0)
    (hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → g ∈ w.toValuationSubring)
    (hord : (C.placeMap P).ord (C.residue ⟨g, hg⟩) = 0) : μ (P.evalAt g) = 1 := by
  obtain ⟨hm, hval, heq⟩ := C.pointwise P hP hPrat g hg hfib
  have hresbar :
      IsLocalRing.residue (C.placeMap P).toValuationSubring ⟨C.residue ⟨g, hg⟩, hm⟩ ≠ 0 := by
    intro h0
    have hpos := GaussReduction.ord_pos_of_residue_eq_zero (C.placeMap P) hm hres h0
    rw [hord] at hpos
    exact lt_irrefl _ hpos
  have hresA : IsLocalRing.residue A ⟨P.evalAt g, hval⟩ ≠ 0 := by
    intro h0
    apply hresbar
    rw [← heq, h0, map_zero]
  have hunit : IsUnit (⟨P.evalAt g, hval⟩ : A) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hresA
  exact abv_coe_eq_one_of_isUnit μ hA hunit

p2m_export "AlgebraicCurve.ComponentChart" "abv_evalAt_eq_one"

open Classical in

private theorem _root_.AlgebraicCurve.ComponentChart.neg_log_abv_evalAt_eq_of_disc [HasPrincipalDivisors L F] (μ : AbsoluteValue L ℝ)
    (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) (hrat : ∀ w ∈ C.dom, w.IsRational)
    {P : Place L F} (hP : P ∈ C.dom) {f : F} (hf : f ≠ 0)
    (D : Divisor L F) (hD : ∀ w, D w = w.ord f) (hDP : D P = 0) (T : F)
    (hdisc : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P →
      ∃ h : T - algebraMap L F (w.evalAt T) ∈ C.integers,
        C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap w).ord (C.residue ⟨_, h⟩) = 1 ∧
        0 < w.ord (T - algebraMap L F (w.evalAt T)) ∧
        ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap w → Q ≠ w →
          Q.ord (T - algebraMap L F (w.evalAt T)) = 0) :
    -Real.log (μ (P.evalAt f)) = -C.logGaussNorm μ f +
      ∑ w ∈ D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P),
        (D w : ℝ) * (-Real.log (μ (P.evalAt T - w.evalAt T))) := by

  set S := D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P) with hS
  have hmemS : ∀ w ∈ S, D w ≠ 0 ∧ w ∈ C.dom ∧ C.placeMap w = C.placeMap P := fun w hw => by
    have hw' := hw
    rw [hS, Finset.mem_filter, Finsupp.mem_support_iff] at hw'
    exact hw'
  have hPrat : P.IsRational := hrat P hP

  set u : Place L F → F := fun w => T - algebraMap L F (w.evalAt T) with hu
  have hu_int : ∀ w ∈ S, ∃ h : u w ∈ C.integers, C.residue ⟨u w, h⟩ ≠ 0 := fun w hw => by
    obtain ⟨h, h1, -, -, -⟩ := hdisc w (hmemS w hw).2.1 (hmemS w hw).2.2
    exact ⟨h, h1⟩
  have hu_ord_self : ∀ w ∈ S, w.ord (u w) = 1 := fun w hw => by
    obtain ⟨h, h1, h2, h3, h4⟩ := hdisc w (hmemS w hw).2.1 (hmemS w hw).2.2
    exact C.ord_eq_one_of_disc (hmemS w hw).2.1 h h1 h2 h3 h4
  have hu_ord_other : ∀ w ∈ S, ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q ≠ w →
      Q.ord (u w) = 0 := fun w hw Q hQ hQmap hne => by
    obtain ⟨-, -, -, -, h4⟩ := hdisc w (hmemS w hw).2.1 (hmemS w hw).2.2
    exact h4 Q hQ (hQmap.trans (hmemS w hw).2.2.symm) hne
  have hu0 : ∀ w ∈ S, u w ≠ 0 := fun w hw =>
    C.coe_ne_zero_of_residue_ne_zero (hu_int w hw).choose_spec

  have hTmem : T ∈ P.toValuationSubring := by
    obtain ⟨-, -, -, h3, -⟩ := hdisc P hP rfl
    have hne : T - algebraMap L F (P.evalAt T) ≠ 0 := by
      intro h0
      rw [h0, Place.ord_zero] at h3
      exact lt_irrefl _ h3
    have hmem := GaussReduction.mem_of_ord_nonneg_gen P hne h3.le
    have hT : T = (T - algebraMap L F (P.evalAt T)) + algebraMap L F (P.evalAt T) := by ring
    rw [hT]
    exact add_mem hmem (P.algebraMap_mem' _)

  obtain ⟨c, hcf, hcres⟩ := C.exists_smul_mem f hf
  have hG : C.logGaussNorm μ f = -Real.log (μ c) := C.logGaussNorm_eq_neg_log μ hA hcf hcres
  have hcf0 : c • f ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hcres
  have hc0 : c ≠ 0 := fun h => hcf0 (by rw [h, zero_smul])

  set g : F := (c • f) * ∏ w ∈ S, u w ^ (-(D w)) with hg
  obtain ⟨hPi, hPires⟩ := C.prod_mem_of_residue_ne_zero S (fun w => u w ^ (-(D w)))
    (fun w hw => C.zpow_mem_of_residue_ne_zero (hu_int w hw).choose (hu_int w hw).choose_spec _)
  have hgint : g ∈ C.integers := mul_mem hcf hPi
  have hgres : C.residue ⟨g, hgint⟩ ≠ 0 := by
    have hsub : (⟨g, hgint⟩ : C.integers) = ⟨c • f, hcf⟩ * ⟨∏ w ∈ S, u w ^ (-(D w)), hPi⟩ :=
      Subtype.ext rfl
    rw [hsub, map_mul]
    exact mul_ne_zero hcres hPires
  have hg0 : g ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hgres
  have hprod0 : (∏ w ∈ S, u w ^ (-(D w))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => zpow_ne_zero _ (hu0 w hw)

  have hordg : ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q.ord g = 0 := by
    intro Q hQ hQmap
    have hordcf : Q.ord (c • f) = Q.ord f := by
      rw [Algebra.smul_def, Q.ord_mul ((_root_.map_ne_zero _).mpr hc0) hf,
        StandardAnnulus.ord_algebraMap_eq_zero Q hc0, zero_add]
    have hordPi : Q.ord (∏ w ∈ S, u w ^ (-(D w))) = ∑ w ∈ S, -(D w) * Q.ord (u w) := by
      rw [Q.ord_finset_prod S (fun w => u w ^ (-(D w))) (fun w hw => zpow_ne_zero _ (hu0 w hw))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Q.ord_zpow]
    rw [hg, Q.ord_mul hcf0 hprod0, hordcf, hordPi]
    by_cases hQS : Q ∈ S
    · rw [Finset.sum_eq_single Q]
      · rw [hu_ord_self Q hQS, mul_one, ← hD Q]
        ring
      · intro w hw hne
        rw [hu_ord_other w hw Q hQ hQmap (Ne.symm hne), mul_zero]
      · intro h
        exact absurd hQS h
    · have hDQ : D Q = 0 := by
        by_contra hne
        apply hQS
        rw [hS, Finset.mem_filter]
        exact ⟨Finsupp.mem_support_iff.mpr hne, hQ, hQmap⟩
      rw [Finset.sum_eq_zero]
      · rw [← hD Q, hDQ, add_zero]
      · intro w hw
        have hne : Q ≠ w := fun h => hQS (h ▸ hw)
        rw [hu_ord_other w hw Q hQ hQmap hne, mul_zero]

  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) g hg0
  have hordres : (C.placeMap P).ord (C.residue ⟨g, hgint⟩) = 0 := by
    rw [C.ord_residue_eq_sum_fibre hgint hgres hP Dg hDg]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [Finset.mem_filter] at hw
    rw [hDg w]
    exact hordg w hw.2.1 hw.2.2
  have hfibg : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → g ∈ w.toValuationSubring :=
    fun w hw hmap => GaussReduction.mem_of_ord_nonneg_gen w hg0 (hordg w hw hmap).ge
  have hone : μ (P.evalAt g) = 1 := C.abv_evalAt_eq_one μ hA hP hPrat hgint hgres hfibg hordres

  have hPS : P ∉ S := fun h => (hmemS P h).1 hDP
  have hfP0 : P.ord f = 0 := by rw [← hD P, hDP]
  have hfmem : f ∈ P.toValuationSubring := GaussReduction.mem_of_ord_nonneg_gen P hf hfP0.ge
  have hcmem : algebraMap L F c ∈ P.toValuationSubring := P.algebraMap_mem' c
  have huP : ∀ w ∈ S, P.ord (u w) = 0 := fun w hw =>
    hu_ord_other w hw P hP rfl (fun h => hPS (h ▸ hw))
  have hzmem : ∀ w ∈ S, u w ^ (-(D w)) ∈ P.toValuationSubring := fun w hw =>
    GaussReduction.mem_of_ord_nonneg_gen P (zpow_ne_zero _ (hu0 w hw))
      (by rw [P.ord_zpow, huP w hw, mul_zero])
  have hΔ : ∀ w ∈ S, P.evalAt (u w) = P.evalAt T - w.evalAt T := fun w hw => by
    show P.evalAt (T - algebraMap L F (w.evalAt T)) = P.evalAt T - w.evalAt T
    rw [GaussReduction.evalAt_sub_of_mem P hPrat hTmem (P.algebraMap_mem' _),
      GaussReduction.evalAt_algebraMap_const P hPrat]
  have hevalg : P.evalAt g
      = c * P.evalAt f * ∏ w ∈ S, (P.evalAt T - w.evalAt T) ^ (-(D w)) := by
    have hcfmem : c • f ∈ P.toValuationSubring := by
      rw [Algebra.smul_def]
      exact mul_mem hcmem hfmem
    rw [hg, GaussReduction.evalAt_mul_of_mem P hPrat hcfmem (prod_mem fun w hw => hzmem w hw),
      Algebra.smul_def, GaussReduction.evalAt_mul_of_mem P hPrat hcmem hfmem,
      GaussReduction.evalAt_algebraMap_const P hPrat c,
      P.evalAt_finset_prod_of_mem hPrat S (fun w => u w ^ (-(D w))) hzmem]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [P.evalAt_zpow_of_ord_eq_zero hPrat (hu0 w hw) (huP w hw), hΔ w hw]

  have hfP : P.evalAt f ≠ 0 := StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero P hPrat hf hfP0
  have hΔ0 : ∀ w ∈ S, P.evalAt T - w.evalAt T ≠ 0 := fun w hw => by
    rw [← hΔ w hw]
    exact StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero P hPrat (hu0 w hw) (huP w hw)
  have hμc : μ c ≠ 0 := μ.ne_zero hc0
  have hμf : μ (P.evalAt f) ≠ 0 := μ.ne_zero hfP
  have hμΔ : ∀ w ∈ S, μ (P.evalAt T - w.evalAt T) ≠ 0 := fun w hw => μ.ne_zero (hΔ0 w hw)

  rw [hevalg, map_mul, map_mul, map_prod] at hone
  have hprodne : (∏ w ∈ S, μ ((P.evalAt T - w.evalAt T) ^ (-(D w)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => by
      rw [map_zpow₀]
      exact zpow_ne_zero _ (hμΔ w hw)
  have hlog := congrArg Real.log hone
  rw [Real.log_one, Real.log_mul (mul_ne_zero hμc hμf) hprodne, Real.log_mul hμc hμf,
    Real.log_prod (fun w hw => by rw [map_zpow₀]; exact zpow_ne_zero _ (hμΔ w hw))] at hlog
  have hterm : ∀ w ∈ S, Real.log (μ ((P.evalAt T - w.evalAt T) ^ (-(D w))))
      = -((D w : ℝ) * Real.log (μ (P.evalAt T - w.evalAt T))) := fun w hw => by
    rw [map_zpow₀, Real.log_zpow]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hlog
  have hsum : ∑ w ∈ S, (D w : ℝ) * (-Real.log (μ (P.evalAt T - w.evalAt T)))
      = -∑ w ∈ S, (D w : ℝ) * Real.log (μ (P.evalAt T - w.evalAt T)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hG, hsum]
  linarith

p2m_export "AlgebraicCurve.ComponentChart" "neg_log_abv_evalAt_eq_of_disc"
end ComponentChart
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField deg ord ord_zero ord_mul ord_inv ord_zpow algebraMap_mem' toValuationSubring IsRational residueInv_algebraMap evalAt evalAt_of_mem evalAt_one"
p2m_open "AlgebraicCurve.Place~exists_ord_eq_one~evalAt_mul_of_mem~evalAt_ne_zero_of_ord_eq_zero~deg_eq_one_of_isRational~residue_algebraMap"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.evalAt_zero' : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_zero'"

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero {f : F} (hmem : f ∈ v.toValuationSubring)
    (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have h0 : f ≠ 0 := by
    rintro rfl
    exact hne v.evalAt_zero'
  rcases lt_or_eq_of_le (GaussReduction.ord_nonneg_of_mem_gen v hmem h0) with hlt | heq
  · exact absurd (StandardAnnulus.evalAt_eq_zero_of_ord_pos v h0 hlt) hne
  · exact heq.symm

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_of_evalAt_ne_zero"
end Place
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff placeMap residue nodes exists_smul_mem pointwise residue_algebraMap ker_residue mapDomain_placeMap placeMap_not_mem_nodes dom"
p2m_open "AlgebraicCurve.ComponentChart"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (C : ComponentChart A F Fbar)

private theorem _root_.AlgebraicCurve.ComponentChart.residue_zpow_mk {u : F} (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0) (n : ℤ)
    (h : u ^ n ∈ C.integers) : C.residue ⟨u ^ n, h⟩ = (C.residue ⟨u, hu⟩) ^ n := by
  have hpow : ∀ (m : ℕ) (hm : u ^ m ∈ C.integers),
      C.residue ⟨u ^ m, hm⟩ = (C.residue ⟨u, hu⟩) ^ m := by
    intro m hm
    have hsub : (⟨u ^ m, hm⟩ : C.integers) = (⟨u, hu⟩ : C.integers) ^ m :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow])
    rw [hsub, map_pow]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · have hm : u ^ m ∈ C.integers := pow_mem hu m
    have hsub : (⟨u ^ (m : ℤ), h⟩ : C.integers) = ⟨u ^ m, hm⟩ :=
      Subtype.ext (show u ^ (m : ℤ) = u ^ m by rw [zpow_natCast])
    rw [hsub, hpow m hm, zpow_natCast]
  · have hm : u ^ m ∈ C.integers := pow_mem hu m
    have hinv : (u ^ m)⁻¹ ∈ C.integers := by
      have h' := h
      rwa [zpow_neg, zpow_natCast] at h'
    have hsub : (⟨u ^ (-(m : ℤ)), h⟩ : C.integers) = ⟨(u ^ m)⁻¹, hinv⟩ :=
      Subtype.ext (show u ^ (-(m : ℤ)) = (u ^ m)⁻¹ by rw [zpow_neg, zpow_natCast])
    rw [hsub]
    have hne : C.residue ⟨u ^ m, hm⟩ ≠ 0 := by
      rw [hpow m hm]
      exact pow_ne_zero _ hres
    have hu0 : u ^ m ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hne
    have hmul : C.residue ⟨(u ^ m)⁻¹, hinv⟩ * C.residue ⟨u ^ m, hm⟩ = 1 := by
      rw [← map_mul, ← map_one C.residue]
      congr 1
      exact Subtype.ext (inv_mul_cancel₀ hu0)
    rw [zpow_neg, zpow_natCast, ← hpow m hm]
    exact eq_inv_of_mul_eq_one_left hmul

p2m_export "AlgebraicCurve.ComponentChart" "residue_zpow_mk"

private theorem _root_.AlgebraicCurve.ComponentChart.residue_algebraMap_eq_zero_of_mem_maximalIdeal {a : L} (haA : a ∈ A)
    (ha : (⟨a, haA⟩ : A) ∈ maximalIdeal A) (h : algebraMap L F a ∈ C.integers) :
    C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have h1 := C.residue_algebraMap ⟨a, haA⟩
  have hsub : (⟨algebraMap L F a, h⟩ : C.integers)
      = ⟨algebraMap L F ((⟨a, haA⟩ : A) : L), (C.algebraMap_mem_iff _).mpr haA⟩ := Subtype.ext rfl
  rw [hsub, h1, (IsLocalRing.residue_eq_zero_iff _).mpr ha, map_zero]

p2m_export "AlgebraicCurve.ComponentChart" "residue_algebraMap_eq_zero_of_mem_maximalIdeal"
end ComponentChart
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_param_sub"
p2m_open "AlgebraicCurve.Annulus"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem _root_.AlgebraicCurve.Annulus.eq_of_evalAt_param_eq (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom)
    (hQ : Q ∈ An.dom) (h : P.evalAt An.param = Q.evalAt An.param) : P = Q := by
  obtain ⟨-, -, ⟨hA', hmax⟩, hne, m, hm, hmod⟩ := An.mem_dom P hP
  obtain ⟨R, -, huniq⟩ :=
    An.existsUnique_evalAt_eq ⟨P.evalAt An.param, hA'⟩ hmax hne ⟨m, hm, hmod⟩
  exact (huniq P ⟨hP, rfl⟩).trans (huniq Q ⟨hQ, h.symm⟩).symm

p2m_export "AlgebraicCurve.Annulus" "eq_of_evalAt_param_eq"

private theorem _root_.AlgebraicCurve.Annulus.ord_param_sub_of_ne (An : Annulus A F) {P w : Place L F} (hP : P ∈ An.dom)
    (hw : w ∈ An.dom) (hne : P ≠ w) :
    P.ord (An.param - algebraMap L F (w.evalAt An.param)) = 0 := by
  obtain ⟨hPrat, hzP, -, -, -⟩ := An.mem_dom P hP
  have hmem : An.param - algebraMap L F (w.evalAt An.param) ∈ P.toValuationSubring :=
    sub_mem hzP (P.algebraMap_mem' _)
  refine P.ord_eq_zero_of_evalAt_ne_zero hmem ?_
  rw [GaussReduction.evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _),
    GaussReduction.evalAt_algebraMap_const P hPrat, sub_ne_zero]
  exact fun h => hne (An.eq_of_evalAt_param_eq hP hw h)

p2m_export "AlgebraicCurve.Annulus" "ord_param_sub_of_ne"
namespace IsAttached

private theorem _root_.AlgebraicCurve.Annulus.IsAttached.exists_param_sub_mem {An : Annulus A F} {C : ComponentChart A F Fbar}
    {x : Place (ResidueField A) Fbar} (hatt : An.IsAttached C x) {w : Place L F} (hw : w ∈ An.dom) :
    ∃ h : An.param - algebraMap L F (w.evalAt An.param) ∈ C.integers,
      C.residue ⟨_, h⟩ = C.residue ⟨An.param, hatt.2.1⟩ := by
  obtain ⟨-, -, ⟨hwA, hwmax⟩, -, -⟩ := An.mem_dom w hw
  have hconst : algebraMap L F (w.evalAt An.param) ∈ C.integers := (C.algebraMap_mem_iff _).mpr hwA
  refine ⟨sub_mem hatt.2.1 hconst, ?_⟩
  have hsub : (⟨An.param - algebraMap L F (w.evalAt An.param), sub_mem hatt.2.1 hconst⟩ : C.integers)
      = ⟨An.param, hatt.2.1⟩ - ⟨algebraMap L F (w.evalAt An.param), hconst⟩ := Subtype.ext rfl
  rw [hsub, map_sub, C.residue_algebraMap_eq_zero_of_mem_maximalIdeal hwA hwmax hconst, sub_zero]

end IsAttached
p2m_export "AlgebraicCurve.Annulus" "IsAttached.exists_param_sub_mem"
namespace IsAttached
open Classical in

private theorem _root_.AlgebraicCurve.Annulus.IsAttached.neg_log_abv_evalAt_eq {An : Annulus A F} {C : ComponentChart A F Fbar}
    {x : Place (ResidueField A) Fbar} (hatt : An.IsAttached C x) (μ : AbsoluteValue L ℝ)
    (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) {f : F} (hf : f ≠ 0) (D : Divisor L F)
    (hD : ∀ w, D w = w.ord f) {c : L} (hcf : c • f ∈ C.integers)
    (hcres : C.residue ⟨c • f, hcf⟩ ≠ 0) {P : Place L F} (hP : P ∈ An.dom) (hDP : D P = 0) :
    -Real.log (μ (P.evalAt f)) = Real.log (μ c)
      + (((x.ord (C.residue ⟨c • f, hcf⟩) : ℤ) : ℝ) - ∑ w ∈ D.support.filter (· ∈ An.dom), (D w : ℝ))
          * (-Real.log (μ (P.evalAt An.param)))
      + ∑ w ∈ D.support.filter (· ∈ An.dom),
          (D w : ℝ) * (-Real.log (μ (P.evalAt An.param - w.evalAt An.param))) := by
  set W := D.support.filter (· ∈ An.dom) with hW
  have hmemW : ∀ w ∈ W, D w ≠ 0 ∧ w ∈ An.dom := fun w hw => by
    have hw' := hw
    rw [hW, Finset.mem_filter, Finsupp.mem_support_iff] at hw'
    exact hw'
  obtain ⟨hPrat, hzP, ⟨hzPA, hzPmax⟩, hzP0, -⟩ := An.mem_dom P hP
  set z := An.param with hz
  set u : Place L F → F := fun w => z - algebraMap L F (w.evalAt z) with hu
  have hu_int : ∀ w ∈ W, ∃ h : u w ∈ C.integers, C.residue ⟨u w, h⟩ = C.residue ⟨z, hatt.2.1⟩ :=
    fun w hw => hatt.exists_param_sub_mem (hmemW w hw).2
  have hzres : C.residue ⟨z, hatt.2.1⟩ ≠ 0 := by
    intro h0
    have h1 := hatt.2.2.1
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hu_res : ∀ w ∈ W, ∃ h : u w ∈ C.integers, C.residue ⟨u w, h⟩ ≠ 0 := fun w hw => by
    obtain ⟨h, heq⟩ := hu_int w hw
    exact ⟨h, by rw [heq]; exact hzres⟩
  have hu0 : ∀ w ∈ W, u w ≠ 0 := fun w hw =>
    C.coe_ne_zero_of_residue_ne_zero (hu_res w hw).choose_spec
  have hu_ord_self : ∀ w ∈ W, w.ord (u w) = 1 := fun w hw => An.ord_param_sub w (hmemW w hw).2
  have hu_ord_other : ∀ w ∈ W, ∀ Q ∈ An.dom, Q ≠ w → Q.ord (u w) = 0 := fun w hw Q hQ hne =>
    An.ord_param_sub_of_ne hQ (hmemW w hw).2 hne

  have hcf0 : c • f ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hcres
  have hc0 : c ≠ 0 := fun h => hcf0 (by rw [h, zero_smul])
  set g : F := (c • f) * ∏ w ∈ W, u w ^ (-(D w)) with hg
  obtain ⟨hPi, hPires⟩ := C.prod_mem_of_residue_ne_zero W (fun w => u w ^ (-(D w)))
    (fun w hw => C.zpow_mem_of_residue_ne_zero (hu_res w hw).choose (hu_res w hw).choose_spec _)
  have hgint : g ∈ C.integers := mul_mem hcf hPi
  have hgsub : (⟨g, hgint⟩ : C.integers) = ⟨c • f, hcf⟩ * ⟨∏ w ∈ W, u w ^ (-(D w)), hPi⟩ :=
    Subtype.ext rfl
  have hgres : C.residue ⟨g, hgint⟩ ≠ 0 := by
    rw [hgsub, map_mul]
    exact mul_ne_zero hcres hPires
  have hg0 : g ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hgres
  have hprod0 : (∏ w ∈ W, u w ^ (-(D w))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => zpow_ne_zero _ (hu0 w hw)

  have hPires_eq : C.residue ⟨∏ w ∈ W, u w ^ (-(D w)), hPi⟩
      = ∏ w ∈ W, (C.residue ⟨z, hatt.2.1⟩) ^ (-(D w)) := by
    have key : ∀ (S : Finset (Place L F)) (hS : S ⊆ W) (hmem : (∏ w ∈ S, u w ^ (-(D w))) ∈ C.integers),
        C.residue ⟨∏ w ∈ S, u w ^ (-(D w)), hmem⟩ = ∏ w ∈ S, (C.residue ⟨z, hatt.2.1⟩) ^ (-(D w)) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro _ hmem
        have hsub : (⟨∏ w ∈ (∅ : Finset (Place L F)), u w ^ (-(D w)), hmem⟩ : C.integers) = 1 :=
          Subtype.ext (show (∏ w ∈ (∅ : Finset (Place L F)), u w ^ (-(D w))) = ((1 : C.integers) : F) by
            rw [Finset.prod_empty]; rfl)
        rw [hsub, map_one, Finset.prod_empty]
      | insert a S ha ih =>
        intro hS hmem
        have haW : a ∈ W := hS (Finset.mem_insert_self a S)
        have hSW : S ⊆ W := fun i hi => hS (Finset.mem_insert_of_mem hi)
        obtain ⟨ha1, ha2⟩ := C.zpow_mem_of_residue_ne_zero (hu_res a haW).choose
          (hu_res a haW).choose_spec (-(D a))
        obtain ⟨hS1, -⟩ := C.prod_mem_of_residue_ne_zero S (fun w => u w ^ (-(D w)))
          (fun w hw => C.zpow_mem_of_residue_ne_zero (hu_res w (hSW hw)).choose
            (hu_res w (hSW hw)).choose_spec _)
        have hsub : (⟨∏ w ∈ insert a S, u w ^ (-(D w)), hmem⟩ : C.integers)
            = ⟨u a ^ (-(D a)), ha1⟩ * ⟨∏ w ∈ S, u w ^ (-(D w)), hS1⟩ :=
          Subtype.ext (Finset.prod_insert ha)
        rw [hsub, map_mul, ih hSW hS1, Finset.prod_insert ha,
          C.residue_zpow_mk (hu_res a haW).choose (hu_res a haW).choose_spec (-(D a)) ha1,
          (hu_int a haW).choose_spec]
    exact key W (subset_refl W) hPi
  have hordres : x.ord (C.residue ⟨g, hgint⟩)
      = x.ord (C.residue ⟨c • f, hcf⟩) - ∑ w ∈ W, D w := by
    rw [hgsub, map_mul, x.ord_mul hcres hPires, hPires_eq,
      x.ord_finset_prod W _ (fun w _ => zpow_ne_zero _ hzres)]
    have : ∑ w ∈ W, x.ord ((C.residue ⟨z, hatt.2.1⟩) ^ (-(D w))) = ∑ w ∈ W, -(D w) := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [x.ord_zpow, hatt.2.2.1, mul_one]
    rw [this, Finset.sum_neg_distrib]
    ring

  have hordg : ∀ Q ∈ An.dom, Q.ord g = 0 := by
    intro Q hQ
    have hordcf : Q.ord (c • f) = Q.ord f := by
      rw [Algebra.smul_def, Q.ord_mul ((_root_.map_ne_zero _).mpr hc0) hf,
        StandardAnnulus.ord_algebraMap_eq_zero Q hc0, zero_add]
    have hordPi : Q.ord (∏ w ∈ W, u w ^ (-(D w))) = ∑ w ∈ W, -(D w) * Q.ord (u w) := by
      rw [Q.ord_finset_prod W (fun w => u w ^ (-(D w))) (fun w hw => zpow_ne_zero _ (hu0 w hw))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Q.ord_zpow]
    rw [hg, Q.ord_mul hcf0 hprod0, hordcf, hordPi]
    by_cases hQW : Q ∈ W
    · rw [Finset.sum_eq_single Q]
      · rw [hu_ord_self Q hQW, mul_one, ← hD Q]
        ring
      · intro w hw hne
        rw [hu_ord_other w hw Q hQ (Ne.symm hne), mul_zero]
      · intro h
        exact absurd hQW h
    · have hDQ : D Q = 0 := by
        by_contra hne
        apply hQW
        rw [hW, Finset.mem_filter]
        exact ⟨Finsupp.mem_support_iff.mpr hne, hQ⟩
      rw [Finset.sum_eq_zero]
      · rw [← hD Q, hDQ, add_zero]
      · intro w hw
        have hne : Q ≠ w := fun h => hQW (h ▸ hw)
        rw [hu_ord_other w hw Q hQ hne, mul_zero]

  obtain ⟨hunitmem, hunit⟩ := hatt.2.2.2 g hgint hgres hordg P hP
  have hone : μ (P.evalAt g * (P.evalAt z) ^ (-(x.ord (C.residue ⟨g, hgint⟩)))) = 1 :=
    abv_coe_eq_one_of_isUnit μ hA hunit

  have hPW : P ∉ W := fun h => (hmemW P h).1 hDP
  have hfP0 : P.ord f = 0 := by rw [← hD P, hDP]
  have hfmem : f ∈ P.toValuationSubring := GaussReduction.mem_of_ord_nonneg_gen P hf hfP0.ge
  have hcmem : algebraMap L F c ∈ P.toValuationSubring := P.algebraMap_mem' c
  have huP : ∀ w ∈ W, P.ord (u w) = 0 := fun w hw =>
    hu_ord_other w hw P hP (fun h => hPW (h ▸ hw))
  have hzmem : ∀ w ∈ W, u w ^ (-(D w)) ∈ P.toValuationSubring := fun w hw =>
    GaussReduction.mem_of_ord_nonneg_gen P (zpow_ne_zero _ (hu0 w hw))
      (by rw [P.ord_zpow, huP w hw, mul_zero])
  have hΔ : ∀ w ∈ W, P.evalAt (u w) = P.evalAt z - w.evalAt z := fun w hw => by
    show P.evalAt (z - algebraMap L F (w.evalAt z)) = P.evalAt z - w.evalAt z
    rw [GaussReduction.evalAt_sub_of_mem P hPrat hzP (P.algebraMap_mem' _),
      GaussReduction.evalAt_algebraMap_const P hPrat]
  have hevalg : P.evalAt g = c * P.evalAt f * ∏ w ∈ W, (P.evalAt z - w.evalAt z) ^ (-(D w)) := by
    have hcfmem : c • f ∈ P.toValuationSubring := by
      rw [Algebra.smul_def]
      exact mul_mem hcmem hfmem
    rw [hg, GaussReduction.evalAt_mul_of_mem P hPrat hcfmem (prod_mem fun w hw => hzmem w hw),
      Algebra.smul_def, GaussReduction.evalAt_mul_of_mem P hPrat hcmem hfmem,
      GaussReduction.evalAt_algebraMap_const P hPrat c,
      P.evalAt_finset_prod_of_mem hPrat W (fun w => u w ^ (-(D w))) hzmem]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [P.evalAt_zpow_of_ord_eq_zero hPrat (hu0 w hw) (huP w hw), hΔ w hw]

  have hfPne : P.evalAt f ≠ 0 := StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero P hPrat hf hfP0
  have hΔ0 : ∀ w ∈ W, P.evalAt z - w.evalAt z ≠ 0 := fun w hw => by
    rw [← hΔ w hw]
    exact StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero P hPrat (hu0 w hw) (huP w hw)
  have hμc : μ c ≠ 0 := μ.ne_zero hc0
  have hμf : μ (P.evalAt f) ≠ 0 := μ.ne_zero hfPne
  have hμz : μ (P.evalAt z) ≠ 0 := μ.ne_zero hzP0
  have hμΔ : ∀ w ∈ W, μ (P.evalAt z - w.evalAt z) ≠ 0 := fun w hw => μ.ne_zero (hΔ0 w hw)

  rw [hordres, hevalg, map_mul, map_mul, map_mul, map_prod, map_zpow₀] at hone
  have hprodne : (∏ w ∈ W, μ ((P.evalAt z - w.evalAt z) ^ (-(D w)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => by
      rw [map_zpow₀]
      exact zpow_ne_zero _ (hμΔ w hw)
  have hzpowne : μ (P.evalAt z) ^ (-(x.ord (C.residue ⟨c • f, hcf⟩) - ∑ w ∈ W, D w)) ≠ 0 :=
    zpow_ne_zero _ hμz
  have hlog := congrArg Real.log hone
  rw [Real.log_one, Real.log_mul (mul_ne_zero (mul_ne_zero hμc hμf) hprodne) hzpowne,
    Real.log_mul (mul_ne_zero hμc hμf) hprodne, Real.log_mul hμc hμf,
    Real.log_prod (fun w hw => by rw [map_zpow₀]; exact zpow_ne_zero _ (hμΔ w hw)),
    Real.log_zpow] at hlog
  have hterm : ∀ w ∈ W, Real.log (μ ((P.evalAt z - w.evalAt z) ^ (-(D w))))
      = -((D w : ℝ) * Real.log (μ (P.evalAt z - w.evalAt z))) := fun w hw => by
    rw [map_zpow₀, Real.log_zpow]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at hlog
  have hsum : ∑ w ∈ W, (D w : ℝ) * (-Real.log (μ (P.evalAt z - w.evalAt z)))
      = -∑ w ∈ W, (D w : ℝ) * Real.log (μ (P.evalAt z - w.evalAt z)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hsum]
  have hcast : ((-(x.ord (C.residue ⟨c • f, hcf⟩) - ∑ w ∈ W, D w) : ℤ) : ℝ)
      = -(((x.ord (C.residue ⟨c • f, hcf⟩) : ℤ) : ℝ) - ∑ w ∈ W, (D w : ℝ)) := by
    push_cast
    ring
  rw [hcast] at hlog
  linear_combination (-1 : ℝ) * hlog

end IsAttached
p2m_export "AlgebraicCurve.Annulus" "IsAttached.neg_log_abv_evalAt_eq"
end Annulus
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff placeMap residue nodes exists_smul_mem pointwise residue_algebraMap ker_residue mapDomain_placeMap placeMap_not_mem_nodes dom"
p2m_open "AlgebraicCurve.ComponentChart"

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (C : ComponentChart A F Fbar)

open Classical in

private theorem _root_.AlgebraicCurve.ComponentChart.exists_mem_fibre_evalAt_eq [HasPrincipalDivisors L F] (hrat : ∀ w ∈ C.dom, w.IsRational)
    {P : Place L F} (hP : P ∈ C.dom) {u : F} (hu : u ∈ C.integers) (hres : C.residue ⟨u, hu⟩ ≠ 0)
    (hord1 : (C.placeMap P).ord (C.residue ⟨u, hu⟩) = 1)
    (hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → u ∈ w.toValuationSubring)
    {a : L} (haA : a ∈ A) (ha : (⟨a, haA⟩ : A) ∈ maximalIdeal A) :
    ∃ Q ∈ C.dom, C.placeMap Q = C.placeMap P ∧ Q.evalAt u = a := by
  have hconst : algebraMap L F a ∈ C.integers := (C.algebraMap_mem_iff _).mpr haA
  have hg : u - algebraMap L F a ∈ C.integers := sub_mem hu hconst
  have hgres : C.residue ⟨u - algebraMap L F a, hg⟩ = C.residue ⟨u, hu⟩ := by
    have hsub : (⟨u - algebraMap L F a, hg⟩ : C.integers) = ⟨u, hu⟩ - ⟨algebraMap L F a, hconst⟩ :=
      Subtype.ext rfl
    rw [hsub, map_sub, C.residue_algebraMap_eq_zero_of_mem_maximalIdeal haA ha hconst, sub_zero]
  have hgres0 : C.residue ⟨u - algebraMap L F a, hg⟩ ≠ 0 := by rw [hgres]; exact hres
  have hg0 : u - algebraMap L F a ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hgres0
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (u - algebraMap L F a) hg0
  have hmass := C.ord_residue_eq_sum_fibre hg hgres0 hP D hD
  rw [hgres, hord1] at hmass

  have hnonneg : ∀ w ∈ D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P), 0 ≤ D w := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [hD w]
    exact GaussReduction.ord_nonneg_of_mem_gen w
      (sub_mem (hfib w hw.2.1 hw.2.2) (w.algebraMap_mem' a)) hg0
  obtain ⟨w, hw, hpos⟩ : ∃ w ∈ D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P),
      0 < D w := by
    by_contra h
    push Not at h
    have hzero : ∑ w ∈ D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P), D w = 0 :=
      Finset.sum_eq_zero fun w hw => le_antisymm (h w hw) (hnonneg w hw)
    rw [hzero] at hmass
    exact one_ne_zero hmass
  rw [Finset.mem_filter] at hw
  refine ⟨w, hw.2.1, hw.2.2, ?_⟩
  have hwrat := hrat w hw.2.1
  have hval : w.evalAt (u - algebraMap L F a) = 0 :=
    StandardAnnulus.evalAt_eq_zero_of_ord_pos w hg0 (by rw [← hD w]; exact hpos)
  rw [GaussReduction.evalAt_sub_of_mem w hwrat (hfib w hw.2.1 hw.2.2) (w.algebraMap_mem' a),
    GaussReduction.evalAt_algebraMap_const w hwrat, sub_eq_zero] at hval
  exact hval

p2m_export "AlgebraicCurve.ComponentChart" "exists_mem_fibre_evalAt_eq"
end ComponentChart
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

open IsLocalRing

private theorem mk_mem_maximalIdeal_iff_abv_lt_one {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) {a : L} (haA : a ∈ A) :
    (⟨a, haA⟩ : A) ∈ maximalIdeal A ↔ μ a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra hge
    rw [not_lt] at hge
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at hge
      exact not_lt.mpr hge one_pos
    have hinv : a⁻¹ ∈ A := (hA _).mpr (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge)
    exact hnu (IsUnit.of_mul_eq_one ⟨a⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0)))
  · intro hlt hu
    exact absurd (abv_coe_eq_one_of_isUnit μ hA hu) (ne_of_lt hlt)

namespace AdaptedCovering

open ReductionGraph

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}
  (Γ : AdaptedCovering pf A F P₀ p s μ)

private theorem modulus_ne_zero (e : Fin pf.m) : ((Γ.an e).modulus : AlgebraicClosure ℚ) ≠ 0 :=
  (Γ.pair e).2.2.1

private theorem an'_dom (e : Fin pf.m) : (Γ.an' e).dom = (Γ.an e).dom := (Γ.pair e).1

private theorem an'_param_mul (e : Fin pf.m) :
    (Γ.an' e).param * (Γ.an e).param
      = algebraMap (AlgebraicClosure ℚ) F ((Γ.an e).modulus : AlgebraicClosure ℚ) :=
  (Γ.pair e).2.2.2

private theorem len_eq (e : Fin pf.m) :
    Γ.len e = -Real.log (μ ((Γ.an e).modulus : AlgebraicClosure ℚ)) := rfl

private theorem retract_of_mem_chart {P : Place (AlgebraicClosure ℚ) F} {i : Fin pf.n}
    (hP : P ∈ (Γ.chart i).dom) : Γ.retract P = Sum.inl i := by
  unfold retract
  exact retraction_eq_inl _ _ _ Γ.covers hP (fun j hj => Γ.chart_unique P i j hP hj)

private theorem retract_of_mem_an {P : Place (AlgebraicClosure ℚ) F} {e : Fin pf.m}
    (hP : P ∈ (Γ.an e).dom) :
    Γ.retract P = Sum.inr (e, -Real.log (μ (P.evalAt (Γ.an e).param))) := by
  unfold retract
  exact retraction_eq_inr _ _ _ Γ.covers (fun e' he' => Γ.an_unique P e e' hP he')
    (fun i hi => Γ.chart_an_disjoint P i e hi hP)

private theorem evalAt_an'_param {e : Fin pf.m} {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ (Γ.an e).dom) :
    P.evalAt (Γ.an' e).param
      = ((Γ.an e).modulus : AlgebraicClosure ℚ) * (P.evalAt (Γ.an e).param)⁻¹ := by
  obtain ⟨hPrat, hz, -, hz0, -⟩ := (Γ.an e).mem_dom P hP
  have hP' : P ∈ (Γ.an' e).dom := by rw [Γ.an'_dom]; exact hP
  obtain ⟨-, hz', -, -, -⟩ := (Γ.an' e).mem_dom P hP'
  have hmul : P.evalAt (Γ.an' e).param * P.evalAt (Γ.an e).param
      = ((Γ.an e).modulus : AlgebraicClosure ℚ) := by
    rw [← GaussReduction.evalAt_mul_of_mem P hPrat hz' hz, Γ.an'_param_mul,
      GaussReduction.evalAt_algebraMap_const P hPrat]
  exact (eq_mul_inv_iff_mul_eq₀ hz0).mpr hmul

private theorem exists_mem_dom_evalAt_eq (e : Fin pf.m) {c : AlgebraicClosure ℚ} (hc1 : μ c < 1)
    (hcπ : μ ((Γ.an e).modulus : AlgebraicClosure ℚ) < μ c) :
    ∃ P, P ∈ (Γ.an e).dom ∧ P.evalAt (Γ.an e).param = c := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcπ
    exact (not_lt.mpr (μ.nonneg _)) hcπ
  have hcA : c ∈ A := (Γ.ball c).mpr hc1.le
  have hcmax : (⟨c, hcA⟩ : A) ∈ maximalIdeal A :=
    (mk_mem_maximalIdeal_iff_abv_lt_one μ Γ.ball hcA).mpr hc1
  set π : AlgebraicClosure ℚ := ((Γ.an e).modulus : AlgebraicClosure ℚ)
  have hle : μ (π * c⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀]
    exact (mul_inv_le_iff₀ (μ.pos hc0)).mpr (by rw [one_mul]; exact hcπ.le)
  have hlt : μ (π * c⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    exact (mul_inv_lt_iff₀ (μ.pos hc0)).mpr (by rw [one_mul]; exact hcπ)
  have hmA : π * c⁻¹ ∈ A := (Γ.ball _).mpr hle
  have hmmax : (⟨π * c⁻¹, hmA⟩ : A) ∈ maximalIdeal A :=
    (mk_mem_maximalIdeal_iff_abv_lt_one μ Γ.ball hmA).mpr hlt
  have hm : ∃ m ∈ maximalIdeal A,
      ((Γ.an e).modulus : AlgebraicClosure ℚ) = ((⟨c, hcA⟩ : A) : AlgebraicClosure ℚ) * m := by
    refine ⟨⟨π * c⁻¹, hmA⟩, hmmax, ?_⟩
    show π = c * (π * c⁻¹)
    rw [mul_comm π c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  obtain ⟨P, hP, hPc⟩ := ((Γ.an e).existsUnique_evalAt_eq ⟨c, hcA⟩ hcmax hc0 hm).exists
  exact ⟨P, hP, hPc⟩

private theorem exists_two_levels (e : Fin pf.m) (W : Finset (Place (AlgebraicClosure ℚ) F)) :
    ∃ P₁ P₂, P₁ ∈ (Γ.an e).dom ∧ P₂ ∈ (Γ.an e).dom ∧ P₁ ∉ W ∧ P₂ ∉ W ∧
      μ (P₁.evalAt (Γ.an e).param) ≠ μ (P₂.evalAt (Γ.an e).param) := by
  classical
  set π : AlgebraicClosure ℚ := ((Γ.an e).modulus : AlgebraicClosure ℚ)
  have hπ0 : π ≠ 0 := Γ.modulus_ne_zero e
  have hπ1 : μ π < 1 := Annulus.abv_modulus_lt_one (Γ.an e) μ Γ.ball hπ0
  have hπpos : 0 < μ π := μ.pos hπ0
  have hroot : ∀ k : ℕ, ∃ c : AlgebraicClosure ℚ, c ^ (k + 2) = π := fun k =>
    IsAlgClosed.exists_pow_nat_eq π (Nat.succ_pos (k + 1))
  choose c hc using hroot
  have hμc : ∀ k, μ (c k) ^ (k + 2) = μ π := fun k => by rw [← map_pow, hc k]
  have hc1 : ∀ k, μ (c k) < 1 := fun k => by
    by_contra hge
    rw [not_lt] at hge
    have h1 : 1 ≤ μ (c k) ^ (k + 2) := one_le_pow₀ hge
    rw [hμc k] at h1
    exact absurd hπ1 (not_lt.mpr h1)
  have hcpos : ∀ k, 0 < μ (c k) := fun k => by
    refine μ.pos fun h => hπ0 ?_
    have h1 := hc k
    rw [h, zero_pow (Nat.succ_ne_zero _)] at h1
    exact h1.symm
  have hcπ : ∀ k, μ π < μ (c k) := fun k => by
    rw [← hμc k, pow_succ]
    calc μ (c k) ^ (k + 1) * μ (c k) < 1 * μ (c k) :=
          mul_lt_mul_of_pos_right (pow_lt_one₀ (μ.nonneg _) (hc1 k) (Nat.succ_ne_zero k))
            (hcpos k)
      _ = μ (c k) := one_mul _
  have hinj : ∀ k j, μ (c k) = μ (c j) → k = j := fun k j hkj => by
    have h1 : μ π ^ (j + 2) = μ π ^ (k + 2) := by
      conv_lhs => rw [← hμc k]
      conv_rhs => rw [← hμc j]
      rw [← pow_mul, ← pow_mul, hkj, mul_comm]
    have h2 : ((j + 2 : ℕ) : ℝ) * Real.log (μ π) = ((k + 2 : ℕ) : ℝ) * Real.log (μ π) := by
      rw [← Real.log_pow, ← Real.log_pow, h1]
    have hlog : Real.log (μ π) ≠ 0 := ne_of_lt (Real.log_neg hπpos hπ1)
    have h3 := mul_right_cancel₀ hlog h2
    have h4 : j + 2 = k + 2 := by exact_mod_cast h3
    omega
  have hP : ∀ k, ∃ P, P ∈ (Γ.an e).dom ∧ P.evalAt (Γ.an e).param = c k := fun k =>
    Γ.exists_mem_dom_evalAt_eq e (hc1 k) (hcπ k)
  choose P hPdom hPval using hP
  have hPinj : ∀ k j, P k = P j → k = j := fun k j h =>
    hinj k j (by rw [← hPval k, ← hPval j, h])
  have hB : ((Finset.range (W.card + 2)).filter (fun k => P k ∈ W)).card ≤ W.card :=
    Finset.card_le_card_of_injOn (fun k => P k) (fun k hk => (Finset.mem_filter.mp hk).2)
      (fun k _ j _ h => hPinj k j h)
  have hsum : ((Finset.range (W.card + 2)).filter (fun k => P k ∈ W)).card
      + ((Finset.range (W.card + 2)).filter (fun k => ¬ P k ∈ W)).card = W.card + 2 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hG2 : 1 < ((Finset.range (W.card + 2)).filter (fun k => ¬ P k ∈ W)).card := by omega
  obtain ⟨k, hk, j, hj, hkj⟩ := Finset.one_lt_card.mp hG2
  refine ⟨P k, P j, hPdom k, hPdom j, (Finset.mem_filter.mp hk).2, (Finset.mem_filter.mp hj).2, ?_⟩
  rw [hPval k, hPval j]
  exact fun h => hkj (hinj k j h)

open Classical in

private theorem end_slopes [HasPrincipalDivisors (AlgebraicClosure ℚ) F] (e : Fin pf.m) {f : F} (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ w, D w = w.ord f)
    {c : AlgebraicClosure ℚ} (hc : c • f ∈ (Γ.chart (Γ.src e)).integers)
    (hcres : (Γ.chart (Γ.src e)).residue ⟨c • f, hc⟩ ≠ 0)
    {c' : AlgebraicClosure ℚ} (hc' : c' • f ∈ (Γ.chart (Γ.tgt e)).integers)
    (hc'res : (Γ.chart (Γ.tgt e)).residue ⟨c' • f, hc'⟩ ≠ 0) :
    ((((Γ.xt e).ord ((Γ.chart (Γ.tgt e)).residue ⟨c' • f, hc'⟩) : ℤ) : ℝ)
        = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ))
          - (((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨c • f, hc⟩) : ℤ) : ℝ)) ∧
    (Real.log (μ c) - Real.log (μ c')
        = -(((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨c • f, hc⟩) : ℤ) : ℝ) * Γ.len e
          + ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom),
              (D w : ℝ) * (Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param))))) := by
  set W := D.support.filter (· ∈ (Γ.an e).dom) with hW
  have hmemW : ∀ w ∈ W, D w ≠ 0 ∧ w ∈ (Γ.an e).dom := fun w hw => by
    have hw' := hw
    rw [hW, Finset.mem_filter, Finsupp.mem_support_iff] at hw'
    exact hw'
  have hDW : ∀ P ∈ (Γ.an e).dom, P ∉ W → D P = 0 := fun P hP hPW => by
    by_contra hne
    exact hPW (by rw [hW, Finset.mem_filter]; exact ⟨Finsupp.mem_support_iff.mpr hne, hP⟩)
  set z : F := (Γ.an e).param
  set π : AlgebraicClosure ℚ := ((Γ.an e).modulus : AlgebraicClosure ℚ)
  set sS : ℝ := (((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨c • f, hc⟩) : ℤ) : ℝ)
  set sT : ℝ := (((Γ.xt e).ord ((Γ.chart (Γ.tgt e)).residue ⟨c' • f, hc'⟩) : ℤ) : ℝ)
  set n : ℝ := ∑ w ∈ W, (D w : ℝ) with hn
  set ℓ : ℝ := Γ.len e
  have hπ0 : π ≠ 0 := Γ.modulus_ne_zero e
  have hℓπ : ℓ = -Real.log (μ π) := rfl

  set v : Place (AlgebraicClosure ℚ) F → ℝ := fun P => -Real.log (μ (P.evalAt z)) with hv
  set K : Place (AlgebraicClosure ℚ) F → Place (AlgebraicClosure ℚ) F → ℝ :=
    fun P w => -Real.log (μ (P.evalAt z - w.evalAt z)) with hK

  have hsrc : ∀ P ∈ (Γ.an e).dom, P ∉ W →
      -Real.log (μ (P.evalAt f)) = Real.log (μ c) + (sS - n) * v P + ∑ w ∈ W, (D w : ℝ) * K P w :=
    fun P hP hPW => (Γ.attached e).1.neg_log_abv_evalAt_eq μ Γ.ball hf D hD hc hcres hP (hDW P hP hPW)

  have htgt : ∀ P ∈ (Γ.an e).dom, P ∉ W →
      -Real.log (μ (P.evalAt f)) = Real.log (μ c')
        + (sT - n) * (-Real.log (μ (P.evalAt (Γ.an' e).param)))
        + ∑ w ∈ W, (D w : ℝ) * (-Real.log (μ (P.evalAt (Γ.an' e).param - w.evalAt (Γ.an' e).param))) := by
    intro P hP hPW
    have hP' : P ∈ (Γ.an' e).dom := by rw [Γ.an'_dom]; exact hP
    have h := (Γ.attached e).2.neg_log_abv_evalAt_eq μ Γ.ball hf D hD hc' hc'res hP' (hDW P hP hPW)
    rw [Γ.an'_dom] at h
    exact h

  have hzval : ∀ P ∈ (Γ.an e).dom, P.evalAt z ≠ 0 := fun P hP => ((Γ.an e).mem_dom P hP).2.2.2.1
  have hv' : ∀ P ∈ (Γ.an e).dom, -Real.log (μ (P.evalAt (Γ.an' e).param)) = ℓ - v P := by
    intro P hP
    have hzP := hzval P hP
    rw [Γ.evalAt_an'_param hP, map_mul, map_inv₀,
      Real.log_mul (μ.ne_zero hπ0) (inv_ne_zero (μ.ne_zero hzP)), Real.log_inv, hℓπ]
    simp only [hv]
    ring
  have hK' : ∀ P ∈ (Γ.an e).dom, ∀ w ∈ (Γ.an e).dom, P ≠ w →
      -Real.log (μ (P.evalAt (Γ.an' e).param - w.evalAt (Γ.an' e).param))
        = ℓ + K P w - v P - v w := by
    intro P hP w hw hne
    have hzP := hzval P hP
    have hzw := hzval w hw
    have hΔ : P.evalAt z - w.evalAt z ≠ 0 :=
      sub_ne_zero.mpr fun h => hne ((Γ.an e).eq_of_evalAt_param_eq hP hw h)
    rw [Γ.evalAt_an'_param hP, Γ.evalAt_an'_param hw]
    have hid : π * (P.evalAt z)⁻¹ - π * (w.evalAt z)⁻¹
        = π * (w.evalAt z - P.evalAt z) * ((P.evalAt z)⁻¹ * (w.evalAt z)⁻¹) := by
      field_simp
    rw [hid, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, AbsoluteValue.map_sub μ (w.evalAt z) (P.evalAt z),
      Real.log_mul (mul_ne_zero (μ.ne_zero hπ0) (μ.ne_zero hΔ))
        (mul_ne_zero (inv_ne_zero (μ.ne_zero hzP)) (inv_ne_zero (μ.ne_zero hzw))),
      Real.log_mul (μ.ne_zero hπ0) (μ.ne_zero hΔ),
      Real.log_mul (inv_ne_zero (μ.ne_zero hzP)) (inv_ne_zero (μ.ne_zero hzw)),
      Real.log_inv, Real.log_inv, hℓπ]
    simp only [hK, hv]
    ring

  set X : ℝ := Real.log (μ c) - Real.log (μ c') - sT * ℓ + ∑ w ∈ W, (D w : ℝ) * v w with hX
  set Y : ℝ := sS + sT - n with hY
  have haff : ∀ P ∈ (Γ.an e).dom, P ∉ W → X + Y * v P = 0 := by
    intro P hP hPW
    have h1 := hsrc P hP hPW
    have h2 := htgt P hP hPW
    rw [hv' P hP] at h2
    have hsum' : ∑ w ∈ W, (D w : ℝ) * (-Real.log (μ (P.evalAt (Γ.an' e).param - w.evalAt (Γ.an' e).param)))
        = ∑ w ∈ W, (D w : ℝ) * (ℓ + K P w - v P - v w) := by
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hK' P hP w (hmemW w hw).2 (fun h => hPW (h ▸ hw))]
    rw [hsum'] at h2
    have hexp : ∑ w ∈ W, (D w : ℝ) * (ℓ + K P w - v P - v w)
        = n * ℓ + (∑ w ∈ W, (D w : ℝ) * K P w) - n * v P - ∑ w ∈ W, (D w : ℝ) * v w := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hn, Finset.sum_mul]
    rw [hexp] at h2
    simp only [hX, hY]
    linear_combination h2 - h1

  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁W, hP₂W, hne⟩ := Γ.exists_two_levels e W
  have hv12 : v P₁ ≠ v P₂ := by
    intro h
    apply hne
    have h' : Real.log (μ (P₁.evalAt z)) = Real.log (μ (P₂.evalAt z)) := by
      have := h
      simp only [hv] at this
      linarith
    exact Real.log_injOn_pos (μ.pos (hzval P₁ hP₁)) (μ.pos (hzval P₂ hP₂)) h'
  have e1 := haff P₁ hP₁ hP₁W
  have e2 := haff P₂ hP₂ hP₂W
  have hY0 : Y = 0 := by
    have h : Y * (v P₁ - v P₂) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hv12
  have hX0 : X = 0 := by
    rw [hY0, zero_mul, add_zero] at e1
    exact e1
  refine ⟨?_, ?_⟩
  ·
    have : sT = n - sS := by
      simp only [hY] at hY0
      linarith
    exact this
  ·
    have hexp : ∑ w ∈ W, (D w : ℝ) * (ℓ - v w) = n * ℓ - ∑ w ∈ W, (D w : ℝ) * v w := by
      simp only [mul_sub, Finset.sum_sub_distrib, hn, Finset.sum_mul]
    have hsT : sT = n - sS := by
      simp only [hY] at hY0
      linarith
    simp only [hX] at hX0
    show Real.log (μ c) - Real.log (μ c') = -sS * ℓ + ∑ w ∈ W, (D w : ℝ) * (ℓ - v w)
    rw [hexp]
    rw [hsT] at hX0
    linear_combination hX0

private def endNode : Fin pf.m ⊕ Fin pf.m → Σ j : Fin pf.n, Place (ResidueField A) (Γ.Fbar j) :=
  Sum.elim (fun e => ⟨Γ.src e, Γ.xs e⟩) (fun e => ⟨Γ.tgt e, Γ.xt e⟩)

@[scoped simp] private theorem endNode_inl (e : Fin pf.m) : Γ.endNode (Sum.inl e) = ⟨Γ.src e, Γ.xs e⟩ := rfl

@[scoped simp] private theorem endNode_inr (e : Fin pf.m) : Γ.endNode (Sum.inr e) = ⟨Γ.tgt e, Γ.xt e⟩ := rfl

private theorem endNode_mem_nodes (E : Fin pf.m ⊕ Fin pf.m) : (Γ.endNode E).2 ∈ (Γ.chart (Γ.endNode E).1).nodes := by
  cases E with
  | inl e => exact (Γ.attached e).1.1
  | inr e => exact (Γ.attached e).2.1

private theorem endNode_injective : Function.Injective Γ.endNode := by
  intro E E' h
  cases E with
  | inl e =>
    rw [endNode_inl] at h
    exact Γ.end_unique (Γ.src e) (Γ.xs e) (Γ.attached e).1.1 (Sum.inl e) E' rfl h.symm
  | inr e =>
    rw [endNode_inr] at h
    exact Γ.end_unique (Γ.tgt e) (Γ.xt e) (Γ.attached e).2.1 (Sum.inr e) E' rfl h.symm

end AdaptedCovering
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace AdaptedCovering

open IsLocalRing ReductionGraph

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}
  (Γ : AdaptedCovering pf A F P₀ p s μ)

open Classical in

private theorem sum_nodes_ord_residue_eq [HasPrincipalDivisors (AlgebraicClosure ℚ) F] (i : Fin pf.n)
    {f : F} (hf : f ≠ 0) (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ w, D w = w.ord f)
    {c : AlgebraicClosure ℚ} (hc : c • f ∈ (Γ.chart i).integers)
    (hcres : (Γ.chart i).residue ⟨c • f, hc⟩ ≠ 0) :
    ∑ x ∈ (Γ.chart i).nodes, x.ord ((Γ.chart i).residue ⟨c • f, hc⟩)
      = -∑ w ∈ D.support.filter (· ∈ (Γ.chart i).dom), D w := by
  set C := Γ.chart i
  set fbar := C.residue ⟨c • f, hc⟩

  haveI := (Γ.res i).1
  obtain ⟨Dbar, hDbar, hdeg⟩ :=
    HasPrincipalDivisors.exists_divisor (K := ResidueField A) fbar hcres
  have hdeg1 : ∀ y : Place (ResidueField A) (Γ.Fbar i), (y.deg : ℤ) = 1 := fun y => by
    simp [OfTopTransport.deg_eq_one_of_isRational y ((Γ.res i).2 y)]
  have hdegsum : Divisor.degree Dbar = ∑ y ∈ Dbar.support, Dbar y := by
    show (Finsupp.liftAddHom fun v : Place (ResidueField A) (Γ.Fbar i) =>
      AddMonoidHom.mulRight (v.deg : ℤ)) Dbar = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    show Dbar y * (y.deg : ℤ) = Dbar y
    rw [hdeg1 y, mul_one]
  rw [hdeg] at hdegsum

  set Di := D.filter (· ∈ C.dom) with hDi
  have hcf0 : c • f ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hcres
  have hc0 : c ≠ 0 := fun h => hcf0 (by rw [h, zero_smul])
  have h1 : ∀ P ∈ C.dom, Di P = P.ord ((⟨c • f, hc⟩ : C.integers) : F) := fun P hP => by
    rw [hDi, Finsupp.filter_apply_pos _ _ hP, hD P]
    show P.ord f = P.ord (c • f)
    rw [Algebra.smul_def, P.ord_mul ((_root_.map_ne_zero _).mpr hc0) hf,
      StandardAnnulus.ord_algebraMap_eq_zero P hc0, zero_add]
  have h2 : ∀ P, P ∉ C.dom → Di P = 0 := fun P hP => by
    rw [hDi, Finsupp.filter_apply_neg _ _ hP]
  have hmd : ∀ y, y ∉ C.nodes → Finsupp.mapDomain C.placeMap Di y = y.ord fbar :=
    fun y hy => C.mapDomain_placeMap ⟨c • f, hc⟩ hcres Di h1 h2 y hy
  set G := Finsupp.mapDomain C.placeMap Di with hG

  rw [← Finset.sum_filter_add_sum_filter_not Dbar.support (· ∈ C.nodes) (fun y => Dbar y)]
    at hdegsum

  have hN : ∑ y ∈ Dbar.support.filter (· ∈ C.nodes), Dbar y = ∑ x ∈ C.nodes, x.ord fbar := by
    rw [Finset.sum_subset (s₁ := Dbar.support.filter (· ∈ C.nodes)) (s₂ := C.nodes)
      (fun y hy => (Finset.mem_filter.mp hy).2)
      (fun y hy2 hy' => by
        have hns : y ∉ Dbar.support := fun h => hy' (Finset.mem_filter.mpr ⟨h, hy2⟩)
        exact Finsupp.notMem_support_iff.mp hns)]
    exact Finset.sum_congr rfl fun x _ => hDbar x

  have hGsupp : ∀ y ∈ G.support, y ∉ C.nodes := by
    intro y hy hyn
    have himg := Finsupp.mapDomain_support hy
    rw [Finset.mem_image] at himg
    obtain ⟨P, hP, hPy⟩ := himg
    have hPdom : P ∈ C.dom := by
      by_contra hnd
      exact (Finsupp.mem_support_iff.mp hP) (h2 P hnd)
    exact C.placeMap_not_mem_nodes P hPdom (hPy ▸ hyn)
  have hO : ∑ y ∈ Dbar.support.filter (fun y => ¬ y ∈ C.nodes), Dbar y
      = ∑ w ∈ D.support.filter (· ∈ C.dom), D w := by
    have hO1 : ∑ y ∈ Dbar.support.filter (fun y => ¬ y ∈ C.nodes), Dbar y
        = ∑ y ∈ Dbar.support.filter (fun y => ¬ y ∈ C.nodes), G y := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hyn := (Finset.mem_filter.mp hy).2
      rw [hDbar y, ← hmd y hyn]
    have hO2 : ∑ y ∈ G.support, G y = ∑ y ∈ Dbar.support.filter (fun y => ¬ y ∈ C.nodes), G y := by
      refine Finset.sum_subset (fun y hy => ?_) (fun y _ hy' => Finsupp.notMem_support_iff.mp hy')
      have hyn := hGsupp y hy
      refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, hyn⟩
      rw [hDbar y, ← hmd y hyn]
      exact Finsupp.mem_support_iff.mp hy
    have hO3 : ∑ y ∈ G.support, G y = ∑ w ∈ Di.support, Di w := by
      have hs : (G.sum fun _ n => n) = Di.sum fun _ n => n := by
        rw [hG]
        exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
      simpa only [Finsupp.sum] using hs
    have hO4 : ∑ w ∈ Di.support, Di w = ∑ w ∈ D.support.filter (· ∈ C.dom), D w := by
      rw [hDi, Finsupp.support_filter]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp hw).2]
    rw [hO1, ← hO2, hO3, hO4]
  rw [hN, hO] at hdegsum
  linarith

private theorem sum_ends_eq_sum_nodes {M : Type*} [AddCommMonoid M]
    (g : (Σ j : Fin pf.n, Place (ResidueField A) (Γ.Fbar j)) → M) (v : Fin pf.n) :
    ∑ E ∈ Finset.univ.filter (fun E => (Γ.endNode E).1 = v), g (Γ.endNode E)
      = ∑ x ∈ (Γ.chart v).nodes, g ⟨v, x⟩ := by
  classical
  have hrhs : ∑ x ∈ (Γ.chart v).nodes, g ⟨v, x⟩
      = ∑ q ∈ ((Γ.chart v).nodes).map (Function.Embedding.sigmaMk v), g q := by
    rw [Finset.sum_map]
    rfl
  rw [hrhs]
  apply Finset.sum_nbij Γ.endNode
  · intro E hE
    rw [Finset.mem_filter] at hE
    rw [Finset.mem_map]
    have key : ∀ q : (Σ j : Fin pf.n, Place (ResidueField A) (Γ.Fbar j)),
        q.2 ∈ (Γ.chart q.1).nodes → q.1 = v →
          ∃ x ∈ (Γ.chart v).nodes, (Function.Embedding.sigmaMk v) x = q := by
      rintro ⟨j, y⟩ hy rfl
      exact ⟨y, hy, rfl⟩
    exact key _ (Γ.endNode_mem_nodes E) hE.2
  · exact fun E _ E' _ h => Γ.endNode_injective h
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hq)
    obtain ⟨e, he | he⟩ := Γ.node_end v x hx
    · refine ⟨Sum.inl e, ?_, he⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, congrArg Sigma.fst he⟩
    · refine ⟨Sum.inr e, ?_, he⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, congrArg Sigma.fst he⟩
  · intro E _
    rfl

private theorem sum_ends_eq_add {M : Type*} [AddCommMonoid M] (g : Fin pf.m ⊕ Fin pf.m → M) (v : Fin pf.n) :
    ∑ E ∈ Finset.univ.filter (fun E => (Γ.endNode E).1 = v), g E
      = (∑ e ∈ Finset.univ.filter (fun e => Γ.src e = v), g (Sum.inl e))
        + ∑ e ∈ Finset.univ.filter (fun e => Γ.tgt e = v), g (Sum.inr e) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]
  rfl

open Classical in

private theorem sum_mul_vertexWeight_retract_eq (D : Divisor (AlgebraicClosure ℚ) F) (v : Fin pf.n) :
    (D.sum fun w n => (n : ℝ) * vertexWeight Γ.src Γ.tgt Γ.len (Γ.retract w) v)
      = (∑ w ∈ D.support.filter (· ∈ (Γ.chart v).dom), (D w : ℝ))
        + (∑ e ∈ Finset.univ.filter (fun e => Γ.src e = v),
            ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom),
              (D w : ℝ) * ((Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param)))) / Γ.len e))
        + (∑ e ∈ Finset.univ.filter (fun e => Γ.tgt e = v),
            ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom),
              (D w : ℝ) * ((-Real.log (μ (w.evalAt (Γ.an e).param))) / Γ.len e)) := by

  have hpt : ∀ w : Place (AlgebraicClosure ℚ) F,
      vertexWeight Γ.src Γ.tgt Γ.len (Γ.retract w) v
        = (if w ∈ (Γ.chart v).dom then (1 : ℝ) else 0)
          + ∑ e, (if w ∈ (Γ.an e).dom then
              ((if Γ.src e = v then
                  (Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param)))) / Γ.len e else 0)
                + (if Γ.tgt e = v then
                  (-Real.log (μ (w.evalAt (Γ.an e).param))) / Γ.len e else 0))
              else 0) := by
    intro w
    rcases Γ.partition w with ⟨j, hj, hjuniq, hnot⟩ | ⟨e₀, he₀, heuniq, hnot⟩
    · rw [Γ.retract_of_mem_chart hj, vertexWeight_inl,
        Finset.sum_eq_zero (fun e _ => if_neg (hnot e)), add_zero]
      by_cases hvj : v = j
      · subst hvj
        rw [if_pos rfl, if_pos hj]
      · rw [if_neg hvj, if_neg (fun h => hvj (hjuniq v h))]
    · rw [Γ.retract_of_mem_an he₀, if_neg (hnot v), zero_add, Finset.sum_eq_single e₀]
      · rw [if_pos he₀, vertexWeight_inr]
        simp only [@eq_comm _ v]
      · intro e _ hne
        exact if_neg (fun h => hne (heuniq e h))
      · intro h
        exact absurd (Finset.mem_univ e₀) h

  unfold Finsupp.sum
  simp only [hpt, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_filter, Finset.sum_add_distrib, add_assoc]
  have hswapS : (∑ x, ∑ a ∈ (D.support.filter (· ∈ (Γ.an x).dom)).filter (fun _ => Γ.src x = v),
      (D a : ℝ) * ((Γ.len x - (-Real.log (μ (a.evalAt (Γ.an x).param)))) / Γ.len x))
      = ∑ x ∈ Finset.univ.filter (fun x => Γ.src x = v), ∑ a ∈ D.support.filter (· ∈ (Γ.an x).dom),
          (D a : ℝ) * ((Γ.len x - (-Real.log (μ (a.evalAt (Γ.an x).param)))) / Γ.len x) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Γ.src x = v
    · rw [if_pos hx, Finset.filter_true_of_mem (fun _ _ => hx)]
    · rw [if_neg hx, Finset.filter_false_of_mem (fun _ _ => hx), Finset.sum_empty]
  have hswapT : (∑ x, ∑ a ∈ (D.support.filter (· ∈ (Γ.an x).dom)).filter (fun _ => Γ.tgt x = v),
      (D a : ℝ) * ((-Real.log (μ (a.evalAt (Γ.an x).param))) / Γ.len x))
      = ∑ x ∈ Finset.univ.filter (fun x => Γ.tgt x = v), ∑ a ∈ D.support.filter (· ∈ (Γ.an x).dom),
          (D a : ℝ) * ((-Real.log (μ (a.evalAt (Γ.an x).param))) / Γ.len x) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Γ.tgt x = v
    · rw [if_pos hx, Finset.filter_true_of_mem (fun _ _ => hx)]
    · rw [if_neg hx, Finset.filter_false_of_mem (fun _ _ => hx), Finset.sum_empty]
  rw [hswapS, hswapT]

private theorem inv_mul_mul_add_eq {ℓ : ℝ} (h : ℓ ≠ 0) (a X : ℝ) : ℓ⁻¹ * (a * ℓ + X) = a + X / ℓ := by
  rw [mul_add, div_eq_mul_inv, mul_comm X ℓ⁻¹]
  congr 1
  rw [mul_comm, mul_assoc, mul_inv_cancel₀ h, mul_one]

private theorem inv_mul_neg_helper {ℓ : ℝ} (h : ℓ ≠ 0) {s n P : ℝ} :
    ℓ⁻¹ * (-(-s * ℓ + (n * ℓ - P))) = -(n - s) + P / ℓ := by
  rw [show -(-s * ℓ + (n * ℓ - P)) = (s - n) * ℓ + P by ring, inv_mul_mul_add_eq h]
  ring

open Classical in

private theorem isGrounded_logGaussNorm [HasPrincipalDivisors (AlgebraicClosure ℚ) F] {f : F} (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ w, D w = w.ord f) :
    IsGrounded Γ.src Γ.tgt Γ.len Γ.cuspIdx
      (fun v => D.sum fun w n => (n : ℝ) * vertexWeight Γ.src Γ.tgt Γ.len (Γ.retract w) v)
      (fun v => (Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart v).logGaussNorm μ f) := by
  refine ⟨sub_self _, fun v _ => ?_⟩

  have hsc : ∀ j : Fin pf.n, ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ (Γ.chart j).integers,
      (Γ.chart j).residue ⟨c • f, h⟩ ≠ 0 := fun j => (Γ.chart j).exists_smul_mem f hf
  choose cs hcs hcsres using hsc
  have hG : ∀ j, (Γ.chart j).logGaussNorm μ f = -Real.log (μ (cs j)) := fun j =>
    (Γ.chart j).logGaussNorm_eq_neg_log μ Γ.ball (hcs j) (hcsres j)

  have hES : ∀ e : Fin pf.m,
      (((Γ.xt e).ord ((Γ.chart (Γ.tgt e)).residue ⟨cs (Γ.tgt e) • f, hcs (Γ.tgt e)⟩) : ℤ) : ℝ) = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ)) - (((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨cs (Γ.src e) • f, hcs (Γ.src e)⟩) : ℤ) : ℝ) ∧
      (Γ.chart (Γ.tgt e)).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f
        = -(((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨cs (Γ.src e) • f, hcs (Γ.src e)⟩) : ℤ) : ℝ) * Γ.len e
          + ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param)))) := by
    intro e
    have h := Γ.end_slopes e hf D hD (hcs (Γ.src e)) (hcsres (Γ.src e)) (hcs (Γ.tgt e))
      (hcsres (Γ.tgt e))
    refine ⟨h.1, ?_⟩
    rw [hG (Γ.tgt e), hG (Γ.src e)]
    have h2 := h.2
    linarith

  refine (sum_conductance_mul_sub_eq Γ.src Γ.tgt Γ.len
    (fun u => (Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart u).logGaussNorm μ f) v).trans ?_
  beta_reduce
  have hS : ∑ e ∈ Finset.univ.filter (fun e => Γ.src e = v), (Γ.len e)⁻¹ *
      (((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart v).logGaussNorm μ f) - ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.tgt e)).logGaussNorm μ f))
      = -(∑ e ∈ Finset.univ.filter (fun e => Γ.src e = v), (((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨cs (Γ.src e) • f, hcs (Γ.src e)⟩) : ℤ) : ℝ))
        + ∑ e ∈ Finset.univ.filter (fun e => Γ.src e = v), ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom),
            (D w : ℝ) * ((Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param)))) / Γ.len e) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hev : Γ.src e = v := (Finset.mem_filter.mp he).2
    have hℓ : Γ.len e ≠ 0 := (Γ.len_pos e).ne'
    subst hev
    have hdiff : ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f) - ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.tgt e)).logGaussNorm μ f)
        = (Γ.chart (Γ.tgt e)).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f := by ring
    have e2 : ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * ((Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param)))) / Γ.len e)
        = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param))))) / Γ.len e := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hdiff, (hES e).2, inv_mul_mul_add_eq hℓ, e2]
  have hT : ∑ e ∈ Finset.univ.filter (fun e => Γ.tgt e = v), (Γ.len e)⁻¹ *
      (((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart v).logGaussNorm μ f) - ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f))
      = -(∑ e ∈ Finset.univ.filter (fun e => Γ.tgt e = v), (((Γ.xt e).ord ((Γ.chart (Γ.tgt e)).residue ⟨cs (Γ.tgt e) • f, hcs (Γ.tgt e)⟩) : ℤ) : ℝ))
        + ∑ e ∈ Finset.univ.filter (fun e => Γ.tgt e = v), ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom),
            (D w : ℝ) * ((-Real.log (μ (w.evalAt (Γ.an e).param))) / Γ.len e) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hev : Γ.tgt e = v := (Finset.mem_filter.mp he).2
    have hℓ : Γ.len e ≠ 0 := (Γ.len_pos e).ne'
    subst hev
    have hdiff : ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.tgt e)).logGaussNorm μ f) - ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f)
        = -((Γ.chart (Γ.tgt e)).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f) := by ring
    have e1 : ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param))))
        = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ)) * Γ.len e
          - ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (-Real.log (μ (w.evalAt (Γ.an e).param))) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    have e2 : ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * ((-Real.log (μ (w.evalAt (Γ.an e).param))) / Γ.len e)
        = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (-Real.log (μ (w.evalAt (Γ.an e).param)))) / Γ.len e := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hdiff, (hES e).2, (hES e).1, e1, e2, inv_mul_neg_helper hℓ]
  have hN : (∑ e ∈ Finset.univ.filter (fun e => Γ.src e = v), (((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨cs (Γ.src e) • f, hcs (Γ.src e)⟩) : ℤ) : ℝ))
      + (∑ e ∈ Finset.univ.filter (fun e => Γ.tgt e = v), (((Γ.xt e).ord ((Γ.chart (Γ.tgt e)).residue ⟨cs (Γ.tgt e) • f, hcs (Γ.tgt e)⟩) : ℤ) : ℝ))
      = -∑ w ∈ D.support.filter (· ∈ (Γ.chart v).dom), (D w : ℝ) := by
    have h1 := Γ.sum_ends_eq_add
      (fun E => (((Γ.endNode E).2.ord ((Γ.chart (Γ.endNode E).1).residue
        ⟨cs (Γ.endNode E).1 • f, hcs (Γ.endNode E).1⟩) : ℤ) : ℝ)) v
    have h2 := Γ.sum_ends_eq_sum_nodes
      (fun q => (((q.2).ord ((Γ.chart q.1).residue ⟨cs q.1 • f, hcs q.1⟩) : ℤ) : ℝ)) v
    have h3 := Γ.sum_nodes_ord_residue_eq v hf D hD (hcs v) (hcsres v)
    have h3' : ∑ x ∈ (Γ.chart v).nodes, (((x.ord ((Γ.chart v).residue ⟨cs v • f, hcs v⟩)) : ℤ) : ℝ)
        = -∑ w ∈ D.support.filter (· ∈ (Γ.chart v).dom), (D w : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) h3
      push_cast at h
      exact h
    simp only [endNode_inl, endNode_inr] at h1 h2
    rw [h1, h3'] at h2
    exact h2
  have hM := Γ.sum_mul_vertexWeight_retract_eq D v
  rw [hS, hT, hM]
  linarith

end AdaptedCovering
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace FixedAlgebraic

variable {L : Type*} [Field L]

private theorem abv_natCast_le_one (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ) (n : ℕ) :
    μ (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (hμ _ _).trans (max_le ih (by rw [map_one]))

private theorem abv_intCast_le_one (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ) (z : ℤ) :
    μ (z : L) ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [Int.cast_natCast]
    exact abv_natCast_le_one μ hμ n
  · rw [Int.cast_neg, μ.map_neg, Int.cast_natCast]
    exact abv_natCast_le_one μ hμ n

private theorem abv_le_one_of_isIntegral (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ) {β : L}
    (hβ : IsIntegral ℤ β) : μ β ≤ 1 := by
  obtain ⟨f, hf, hfβ⟩ := hβ
  by_contra hgt
  rw [not_le] at hgt
  have hβpos : 0 < μ β := one_pos.trans hgt

  have hsum : β ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, ((f.coeff i : ℤ) : L) * β ^ i := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul]
      at hfβ
    have h : β ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ L) (f.coeff i) * β ^ i :=
      by linear_combination hfβ
    rw [h]
    rfl
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · rw [h0, pow_zero, Finset.range_zero, Finset.sum_empty, neg_zero] at hsum
    exact one_ne_zero hsum
  have hne : (Finset.range f.natDegree).Nonempty := ⟨0, Finset.mem_range.mpr hpos⟩

  have hle : μ (β ^ f.natDegree) ≤ μ β ^ (f.natDegree - 1) := by
    rw [hsum, μ.map_neg]
    refine (IsNonarchimedean.apply_sum_le_sup hμ hne).trans (Finset.sup'_le hne _ fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc μ ((f.coeff i : ℤ) : L) * μ β ^ i ≤ 1 * μ β ^ i :=
          mul_le_mul_of_nonneg_right (abv_intCast_le_one μ hμ _) (pow_nonneg hβpos.le _)
      _ = μ β ^ i := one_mul _
      _ ≤ μ β ^ (f.natDegree - 1) := pow_le_pow_right₀ hgt.le (by omega)
  rw [map_pow] at hle
  have hn : f.natDegree = (f.natDegree - 1) + 1 := by omega
  rw [hn, pow_succ] at hle
  have hpowpos : 0 < μ β ^ (f.natDegree - 1) := pow_pos hβpos _
  have h1 : μ β ≤ 1 := by
    have := (mul_le_iff_le_one_right hpowpos).mp hle
    exact this
  exact absurd h1 (not_le.mpr hgt)

private theorem abv_natCast_eq_one_of_coprime (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ) {p m : ℕ}
    (hμp : μ (p : L) < 1) (hpm : Nat.Coprime p m) : μ (m : L) = 1 := by
  refine le_antisymm (abv_natCast_le_one μ hμ m) ?_
  have hbez : ((p : ℤ) : L) * (Nat.gcdA p m : L) + ((m : ℤ) : L) * (Nat.gcdB p m : L) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p m
    rw [Nat.Coprime.gcd_eq_one hpm] at h
    have h' := congrArg (fun z : ℤ => (z : L)) h
    push_cast at h' ⊢
    linear_combination -h'
  have h1 : (1 : ℝ) ≤ max (μ (((p : ℤ) : L) * (Nat.gcdA p m : L))) (μ (((m : ℤ) : L) * (Nat.gcdB p m : L))) := by
    rw [← μ.map_one, ← hbez]
    exact hμ _ _
  rw [map_mul, map_mul, Int.cast_natCast, Int.cast_natCast] at h1
  have hA := abv_intCast_le_one μ hμ (Nat.gcdA p m)
  have hB := abv_intCast_le_one μ hμ (Nat.gcdB p m)
  have hp1 : μ (p : L) * μ ((Nat.gcdA p m : ℤ) : L) < 1 := by
    calc μ (p : L) * μ ((Nat.gcdA p m : ℤ) : L) ≤ μ (p : L) * 1 :=
          mul_le_mul_of_nonneg_left hA (μ.nonneg _)
      _ < 1 := by rw [mul_one]; exact hμp
  rcases le_max_iff.mp h1 with h | h
  · exact absurd h (not_le.mpr hp1)
  · calc (1 : ℝ) ≤ μ (m : L) * μ ((Nat.gcdB p m : ℤ) : L) := h
      _ ≤ μ (m : L) * 1 := mul_le_mul_of_nonneg_left hB (μ.nonneg _)
      _ = μ (m : L) := mul_one _

private theorem neg_log_abv_intCast (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ) {p : ℕ} (hp : p.Prime)
    (hμp : μ (p : L) < 1) {y : ℤ} (hy : y ≠ 0) :
    -Real.log (μ (y : L)) = (y.natAbs.factorization p : ℝ) * (-Real.log (μ (p : L))) := by
  have hyabs : μ (y : L) = μ ((y.natAbs : ℤ) : L) := by
    rcases Int.natAbs_eq y with h | h
    · rw [← h]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, μ.map_neg]
  rw [hyabs, Int.cast_natCast]
  set n := y.natAbs with hn
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hy
  have hdecomp : (p ^ n.factorization p * (n / p ^ n.factorization p) : ℕ) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : Nat.Coprime p (n / p ^ n.factorization p) := Nat.coprime_ordCompl hp hn0
  conv_lhs => rw [← hdecomp]
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, abv_natCast_eq_one_of_coprime μ hμ hμp hcop,
    mul_one, Real.log_pow]
  ring

private theorem exists_abs_log_abv_le {p : ℕ} (hp : p.Prime) (α : AlgebraicClosure ℚ) (hα : α ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
        |Real.log (μ α)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  have halg : ∀ z : AlgebraicClosure ℚ, IsAlgebraic ℤ z := fun z =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy0, hy⟩ := (halg α).exists_integral_multiple
  obtain ⟨y', hy0', hy'⟩ := (halg α⁻¹).exists_integral_multiple
  refine ⟨(y.natAbs.factorization p : ℝ) + (y'.natAbs.factorization p : ℝ), by positivity, ?_⟩
  intro μ hμ hμp
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hμpos : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) := neg_nonneg.mpr (Real.log_nonpos hμpos.le hμp.le)
  have hαpos : 0 < μ α := μ.pos hα
  have hyc : ((y : ℤ) : AlgebraicClosure ℚ) ≠ 0 := Int.cast_ne_zero.mpr hy0
  have hyc' : ((y' : ℤ) : AlgebraicClosure ℚ) ≠ 0 := Int.cast_ne_zero.mpr hy0'
  have hypos : 0 < μ (y : AlgebraicClosure ℚ) := μ.pos hyc
  have hy'pos : 0 < μ (y' : AlgebraicClosure ℚ) := μ.pos hyc'
  have hvy := neg_log_abv_intCast μ hμ hp hμp hy0
  have hvy' := neg_log_abv_intCast μ hμ hp hμp hy0'

  have hup : Real.log (μ α) ≤ (y.natAbs.factorization p : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    have h1 : μ ((y : AlgebraicClosure ℚ) * α) ≤ 1 := by
      have h := abv_le_one_of_isIntegral μ hμ hy
      rwa [Algebra.smul_def, eq_intCast] at h
    rw [map_mul] at h1
    have h2 := Real.log_nonpos (mul_nonneg (μ.nonneg _) (μ.nonneg _)) h1
    rw [Real.log_mul (ne_of_gt hypos) (ne_of_gt hαpos)] at h2
    rw [← hvy]
    linarith

  have hlow : -((y'.natAbs.factorization p : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ≤ Real.log (μ α) := by
    have h1 : μ ((y' : AlgebraicClosure ℚ) * α⁻¹) ≤ 1 := by
      have h := abv_le_one_of_isIntegral μ hμ hy'
      rwa [Algebra.smul_def, eq_intCast] at h
    rw [map_mul, map_inv₀] at h1
    have h2 := Real.log_nonpos (mul_nonneg (μ.nonneg _) (inv_nonneg.mpr (μ.nonneg _))) h1
    rw [Real.log_mul (ne_of_gt hy'pos) (inv_ne_zero (ne_of_gt hαpos)), Real.log_inv] at h2
    rw [← hvy']
    linarith
  have ha : 0 ≤ (y.natAbs.factorization p : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) :=
    mul_nonneg (by positivity) hlam
  have ha' : 0 ≤ (y'.natAbs.factorization p : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) :=
    mul_nonneg (by positivity) hlam
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end FixedAlgebraic
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.deg Place.ord_zero Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff genusFF prox regVal pivotIndex evalVec GaussReduction.ord_nonneg_of_mem_gen GaussReduction.ord_pos_of_residue_eq_zero GaussReduction.mem_of_ord_nonneg_gen GaussReduction.evalAt_mul_of_mem GaussReduction.evalAt_sub_of_mem GaussReduction.evalAt_algebraMap_const StandardAnnulus.evalAt_eq_zero_of_ord_pos StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero StandardAnnulus.evalAt_inv_of_ord_eq_zero StandardAnnulus.ord_algebraMap_eq_zero ell"
p2m_open "AlgebraicCurve"

namespace EmbSeparation

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem laurentBaseChange_eq_adjoin (N : ℕ) [NeZero N] :
    laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          (⇑(coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions N) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
    (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ IntermediateField.adjoin ℚ (divisorExpansions N) := hy
    induction hy' using IntermediateField.adjoin_induction with
    | mem z hz =>
      exact IntermediateField.subset_adjoin _ _ ⟨z, hz, rfl⟩
    | algebraMap a =>
      rw [eq_ratCast, map_ratCast]
      simp
    | add a b ha hb hia hib =>
      rw [map_add]; exact add_mem (hia ha) (hib hb)
    | mul a b ha hb hia hib =>
      rw [map_mul]; exact mul_mem (hia ha) (hib hb)
    | inv a ha hia =>
      rw [map_inv₀]; exact inv_mem (hia ha)
  · rintro x ⟨y, hy, rfl⟩
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (IntermediateField.subset_adjoin ℚ _ hy)

private theorem image_coeffEmb_divisorExpansions (N : ℕ) [NeZero N] :
    ⇑(coeffEmb (AlgebraicClosure ℚ)) '' divisorExpansions N
      = divisorExpansionsC (AlgebraicClosure ℚ) N := by
  have key : ∀ (d : ℕ) [NeZero d], coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)
      = qExpand (AlgebraicClosure ℚ) d (jqModC (AlgebraicClosure ℚ)) := by
    intro d _
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ d (jqModC ℚ)) = _
    rw [coeffMap_qExpand, coeffMap_jqModC]
  ext x
  constructor
  · rintro ⟨y, ⟨d, hd, hdN, rfl⟩, rfl⟩
    exact ⟨d, hd, hdN, key d⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact ⟨qExpand ℚ d jq, ⟨d, hd, hdN, rfl⟩, key d⟩

private theorem modularFunctionFieldBar_eq_fullC (N : ℕ) [NeZero N] :
    modularFunctionFieldBar N = modularFunctionFieldFullC (AlgebraicClosure ℚ) N := by
  show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) = _
  rw [laurentBaseChange_eq_adjoin, image_coeffEmb_divisorExpansions]
  rfl

private theorem ell_eq_degree_add_one_sub_genusFF (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  have key : ∀ X : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)),
      X = modularFunctionFieldFullC (AlgebraicClosure ℚ) N →
      ∀ D' : Divisor (AlgebraicClosure ℚ) X,
        2 * (genusFF (AlgebraicClosure ℚ) X : ℤ) - 1 ≤ Divisor.degree D' →
        (ell D' : ℤ) = Divisor.degree D' + 1 - (genusFF (AlgebraicClosure ℚ) X : ℤ) := by
    rintro X rfl D' hD'
    exact ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC (AlgebraicClosure ℚ) N D' hD'
  exact key _ (modularFunctionFieldBar_eq_fullC N) D hD

private theorem riemannRochSpace_mono {K F : Type*} [Field K] [Field F] [Algebra K F] {D D' : Divisor K F}
    (h : D ≤ D') : riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (h v)).trans h1)

private theorem exists_mem_notMem_sub_single (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1
      ≤ Divisor.degree (D - Finsupp.single v (1 : ℤ))) :
    ∃ u ∈ riemannRochSpace D, u ∉ riemannRochSpace (D - Finsupp.single v (1 : ℤ)) := by
  have hdeg1 : Divisor.degree (D - Finsupp.single v (1 : ℤ)) = Divisor.degree D - 1 := by
    rw [map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N v]
    simp
  have h1 := ell_eq_degree_add_one_sub_genusFF N D (by rw [hdeg1] at hD; linarith)
  have h2 := ell_eq_degree_add_one_sub_genusFF N (D - Finsupp.single v (1 : ℤ)) hD
  by_contra hcon
  push Not at hcon
  have hle : riemannRochSpace D ≤ riemannRochSpace (D - Finsupp.single v (1 : ℤ)) := fun u hu => hcon u hu
  have hge : riemannRochSpace (D - Finsupp.single v (1 : ℤ)) ≤ riemannRochSpace D :=
    riemannRochSpace_mono (sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one))
  have heq : riemannRochSpace (D - Finsupp.single v (1 : ℤ)) = riemannRochSpace D := le_antisymm hge hle
  have hell : (ell (D - Finsupp.single v (1 : ℤ)) : ℤ) = ell D := by
    show ((Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace (D - Finsupp.single v (1 : ℤ))) : ℕ) : ℤ)
      = ((Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D) : ℕ) : ℤ)
    rw [heq]
  rw [hell, h1, hdeg1] at h2
  linarith

variable (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)

private theorem isRational (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational := by
  intro z
  have h : v.deg = 1 := deg_eq_one_modularFunctionFieldBar N v
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra (AlgebraicClosure ℚ) v.ResidueField) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra (AlgebraicClosure ℚ) v.ResidueField) := by
    rw [hbt]
    exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

private theorem degree_embDivisor_sub_sub (P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Divisor.degree (embDivisor N - Finsupp.single P (1 : ℤ) - Finsupp.single Q (1 : ℤ))
      = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 := by
  unfold embDivisor embDegree
  rw [map_sub, map_sub, map_zsmul, Divisor.degree_single, Divisor.degree_single, Divisor.degree_single,
    deg_eq_one_modularFunctionFieldBar N P, deg_eq_one_modularFunctionFieldBar N Q,
    deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N)]
  push_cast
  ring

variable {N s}

omit [NeZero N] in
open Classical in

private theorem mem_sub_single_of_lt_ord {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} {f : modularFunctionFieldBar N}
    (hf : f ∈ riemannRochSpace D) (hv : f = 0 ∨ -D v < v.ord f) :
    f ∈ riemannRochSpace (D - Finsupp.single v (1 : ℤ)) := by
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro w
  rcases hv with h0 | hlt
  · exact Or.inl h0
  rcases hf w with h0 | hw
  · exact Or.inl h0
  right
  rw [Finsupp.sub_apply, Finsupp.single_apply]
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl]
    omega
  · rw [if_neg hvw, sub_zero]
    exact hw

omit [NeZero N] in

private theorem ord_eq_of_mem_of_notMem {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} {f : modularFunctionFieldBar N}
    (hf : f ∈ riemannRochSpace D) (hfn : f ∉ riemannRochSpace (D - Finsupp.single v (1 : ℤ))) :
    f ≠ 0 ∧ v.ord f = -D v := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hfn (Submodule.zero_mem _)
  refine ⟨hf0, ?_⟩
  have hge : -D v ≤ v.ord f := by
    rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
    · exact absurd h hf0
    · exact h
  by_contra hne
  exact hfn (mem_sub_single_of_lt_ord hf (Or.inr (lt_of_le_of_ne hge (Ne.symm hne))))

private theorem exists_ord_eq_one (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ u : modularFunctionFieldBar N, P.ord u = 1 := by
  classical
  obtain ⟨u₁, hu₁, hu₁n⟩ := exists_mem_notMem_sub_single N (embDivisor N) P (by
    have h := degree_embDivisor_sub_sub N P P
    rw [map_sub (Divisor.degree) (embDivisor N - Finsupp.single P (1 : ℤ))] at h
    have h0 : (0 : ℤ) ≤ Divisor.degree (Finsupp.single P (1 : ℤ) : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar N)) := by
      rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp
    linarith)
  obtain ⟨u₂, hu₂, hu₂n⟩ := exists_mem_notMem_sub_single N (embDivisor N - Finsupp.single P (1 : ℤ)) P
    (le_of_eq (degree_embDivisor_sub_sub N P P).symm)
  obtain ⟨h10, hord1⟩ := ord_eq_of_mem_of_notMem hu₁ hu₁n
  obtain ⟨h20, hord2⟩ := ord_eq_of_mem_of_notMem hu₂ hu₂n
  rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at hord2
  refine ⟨u₂ * u₁⁻¹, ?_⟩
  rw [P.ord_mul h20 (inv_ne_zero h10), P.ord_inv, hord1, hord2]
  ring

variable (hs : IsEmbBasis N s)
include hs

private theorem basis_mem (j : Fin r) : s j ∈ riemannRochSpace (embDivisor N) := by
  rw [← hs.2]
  exact Submodule.subset_span ⟨j, rfl⟩

private theorem pos_of_isEmbBasis : 0 < r := by
  obtain ⟨u, hu, hun⟩ := exists_mem_notMem_sub_single N (embDivisor N) (cuspInftyBar N) (by
    have h := degree_embDivisor_sub_sub N (cuspInftyBar N) (cuspInftyBar N)
    rw [map_sub] at h
    have h0 : (0 : ℤ) ≤ Divisor.degree (Finsupp.single (cuspInftyBar N) (1 : ℤ) : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar N)) := by
      rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp
    linarith)
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exfalso
    have hbot : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = ⊥ := by
      rw [Set.range_eq_empty s, Submodule.span_empty]
    rw [← hs.2, hbot, Submodule.mem_bot] at hu
    subst hu
    exact hun (Submodule.zero_mem _)
  · exact hr

private theorem ord_pivot_eq (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    v.ord (s (pivotIndex s v (pos_of_isEmbBasis hs))) = -embDivisor N v := by
  classical
  have hr := pos_of_isEmbBasis hs

  have hex : ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i))
      ⟨⟨0, hr⟩, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  have hpiv : ∀ j, v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
    unfold pivotIndex
    rw [dif_pos hex]
    exact Classical.choose_spec hex

  have hge : ∀ j, -embDivisor N v ≤ v.ord (s j) := fun j => by
    rcases (mem_riemannRochSpace_iff.mp (basis_mem hs j)) v with h | h
    · exact absurd h (hs.1.ne_zero j)
    · exact h

  obtain ⟨u, hu, hun⟩ := exists_mem_notMem_sub_single N (embDivisor N) v (by
    have h := degree_embDivisor_sub_sub N v v
    rw [map_sub (Divisor.degree) (embDivisor N - Finsupp.single v (1 : ℤ))] at h
    have h0 : (0 : ℤ) ≤ Divisor.degree (Finsupp.single v (1 : ℤ) : Divisor (AlgebraicClosure ℚ)
        (modularFunctionFieldBar N)) := by
      rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; simp
    linarith)
  have hex2 : ∃ j, v.ord (s j) ≤ -embDivisor N v := by
    by_contra hall
    push Not at hall
    apply hun
    have hsub : ∀ j, s j ∈ riemannRochSpace (embDivisor N - Finsupp.single v (1 : ℤ)) := fun j =>
      mem_sub_single_of_lt_ord (basis_mem hs j) (Or.inr (hall j))
    have hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range s)
        ≤ riemannRochSpace (embDivisor N - Finsupp.single v (1 : ℤ)) :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr hsub)
    rw [hs.2] at hspan
    exact hspan hu
  obtain ⟨j, hj⟩ := hex2
  exact le_antisymm ((hpiv j).trans hj) (hge _)

private theorem mul_inv_pivot_mem {f : modularFunctionFieldBar N} (hf : f ∈ riemannRochSpace (embDivisor N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    f * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹ ∈ v.toValuationSubring := by
  by_cases hf0 : f = 0
  · rw [hf0, zero_mul]
    exact zero_mem _
  have hk0 : s (pivotIndex s v (pos_of_isEmbBasis hs)) ≠ 0 := hs.1.ne_zero _
  refine GaussReduction.mem_of_ord_nonneg_gen v (mul_ne_zero hf0 (inv_ne_zero hk0)) ?_
  rw [v.ord_mul hf0 (inv_ne_zero hk0), v.ord_inv, ord_pivot_eq hs v]
  rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
  · exact absurd h hf0
  · omega

private theorem evalAt_add_mul_inv_pivot (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {f g : modularFunctionFieldBar N} (hf : f ∈ riemannRochSpace (embDivisor N))
    (hg : g ∈ riemannRochSpace (embDivisor N)) :
    v.evalAt ((f + g) * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹)
      = v.evalAt (f * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹)
        + v.evalAt (g * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹) := by
  have hvrat := isRational N v
  have hfm := mul_inv_pivot_mem hs hf v
  have hgm := mul_inv_pivot_mem hs hg v
  have h0 : (0 : modularFunctionFieldBar N) ∈ v.toValuationSubring := zero_mem _
  rw [add_mul, show f * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹
      + g * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹
      = f * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹
        - (0 - g * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹) by ring,
    GaussReduction.evalAt_sub_of_mem v hvrat hfm (sub_mem h0 hgm),
    GaussReduction.evalAt_sub_of_mem v hvrat h0 hgm,
    show (0 : modularFunctionFieldBar N) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 0
      by rw [map_zero], GaussReduction.evalAt_algebraMap_const v hvrat]
  ring

private theorem evalAt_smul_mul_inv_pivot (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {f : modularFunctionFieldBar N} (hf : f ∈ riemannRochSpace (embDivisor N)) (a : AlgebraicClosure ℚ) :
    v.evalAt ((a • f) * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹)
      = a * v.evalAt (f * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹) := by
  have hvrat := isRational N v
  rw [Algebra.smul_def, mul_assoc,
    GaussReduction.evalAt_mul_of_mem v hvrat (v.algebraMap_mem' a) (mul_inv_pivot_mem hs hf v),
    GaussReduction.evalAt_algebraMap_const v hvrat]

private theorem evalAt_sum_smul_mul_inv_pivot (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (a : Fin r → AlgebraicClosure ℚ) :
    v.evalAt ((∑ j, a j • s j) * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹)
      = ∑ j, a j * evalVec s v j := by
  classical
  have hvrat := isRational N v
  have hev : ∀ j, evalVec s v j = v.evalAt (s j * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹) := by
    intro j
    unfold evalVec
    rw [dif_pos (pos_of_isEmbBasis hs)]
  simp only [hev]

  have key : ∀ T : Finset (Fin r),
      v.evalAt ((∑ j ∈ T, a j • s j) * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹)
        = ∑ j ∈ T, a j * v.evalAt (s j * (s (pivotIndex s v (pos_of_isEmbBasis hs)))⁻¹) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, zero_mul,
        show (0 : modularFunctionFieldBar N) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 0
          by rw [map_zero], GaussReduction.evalAt_algebraMap_const v hvrat]
    | insert j T hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        evalAt_add_mul_inv_pivot hs v (Submodule.smul_mem _ _ (basis_mem hs j))
          (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (basis_mem hs i)),
        evalAt_smul_mul_inv_pivot hs v (basis_mem hs j), ih]
  exact key Finset.univ

private theorem evalVec_pivot (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    evalVec s v (pivotIndex s v (pos_of_isEmbBasis hs)) = 1 := by
  classical
  unfold evalVec
  rw [dif_pos (pos_of_isEmbBasis hs), mul_inv_cancel₀ (hs.1.ne_zero _),
    show (1 : modularFunctionFieldBar N) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 1
      by rw [map_one], GaussReduction.evalAt_algebraMap_const v (isRational N v)]

set_option maxHeartbeats 1600000 in

private theorem exists_evalVec_mul_ne_of_ne {P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hPQ : P ≠ Q) : ∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i := by
  classical
  have hr := pos_of_isEmbBasis hs

  obtain ⟨u, hu, hun⟩ := exists_mem_notMem_sub_single N (embDivisor N - Finsupp.single P (1 : ℤ)) Q
    (le_of_eq (degree_embDivisor_sub_sub N P Q).symm)
  have huE : u ∈ riemannRochSpace (embDivisor N) :=
    riemannRochSpace_mono (sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one)) hu
  obtain ⟨hu0, hordQ⟩ := ord_eq_of_mem_of_notMem hu hun
  rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg hPQ, sub_zero] at hordQ
  have hordP : -embDivisor N P + 1 ≤ P.ord u := by
    rcases (mem_riemannRochSpace_iff.mp hu) P with h | h
    · exact absurd h hu0
    · rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at h
      omega

  obtain ⟨a, hau⟩ : ∃ a : Fin r → AlgebraicClosure ℚ, ∑ j, a j • s j = u := by
    have h : u ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by rw [hs.2]; exact huE
    exact (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp h

  have hP0 : ∑ j, a j * evalVec s P j = 0 := by
    rw [← evalAt_sum_smul_mul_inv_pivot hs P a, hau]
    have hkP : s (pivotIndex s P hr) ≠ 0 := hs.1.ne_zero _
    apply StandardAnnulus.evalAt_eq_zero_of_ord_pos P (mul_ne_zero hu0 (inv_ne_zero hkP))
    rw [P.ord_mul hu0 (inv_ne_zero hkP), P.ord_inv, ord_pivot_eq hs P]
    omega
  have hQ0 : ∑ j, a j * evalVec s Q j ≠ 0 := by
    rw [← evalAt_sum_smul_mul_inv_pivot hs Q a, hau]
    have hkQ : s (pivotIndex s Q hr) ≠ 0 := hs.1.ne_zero _
    apply StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero Q (isRational N Q)
      (mul_ne_zero hu0 (inv_ne_zero hkQ))
    rw [Q.ord_mul hu0 (inv_ne_zero hkQ), Q.ord_inv, ord_pivot_eq hs Q, hordQ]
    omega

  by_contra hall
  push Not at hall
  apply hQ0
  have hprop : ∀ i, evalVec s Q i = evalVec s P i * evalVec s Q (pivotIndex s P hr) := by
    intro i
    have h := hall i (pivotIndex s P hr)
    rw [evalVec_pivot hs P, one_mul] at h
    exact h.symm
  calc ∑ j, a j * evalVec s Q j
      = (∑ j, a j * evalVec s P j) * evalVec s Q (pivotIndex s P hr) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [hprop j]; ring
    _ = 0 := by rw [hP0, zero_mul]

omit [NeZero N] hs in

private theorem smul_mem_valuationSubring (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (c : AlgebraicClosure ℚ) {x : modularFunctionFieldBar N} (hx : x ∈ v.toValuationSubring) :
    c • x ∈ v.toValuationSubring := by
  rw [Algebra.smul_def]
  exact mul_mem (v.algebraMap_mem' c) hx

set_option maxHeartbeats 1600000 in
omit hs in

private theorem evalAt_sum_smul_of_mem (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {ι : Type*} (T : Finset ι) (a : ι → AlgebraicClosure ℚ) (f : ι → modularFunctionFieldBar N)
    (hf : ∀ j ∈ T, f j ∈ v.toValuationSubring) :
    v.evalAt (∑ j ∈ T, a j • f j) = ∑ j ∈ T, a j * v.evalAt (f j) := by
  classical
  have hvrat := isRational N v
  have hzero : v.evalAt (0 : modularFunctionFieldBar N) = 0 := by
    rw [show (0 : modularFunctionFieldBar N)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) 0 by rw [map_zero],
      GaussReduction.evalAt_algebraMap_const v hvrat]
  have hadd : ∀ {x y : modularFunctionFieldBar N}, x ∈ v.toValuationSubring →
      y ∈ v.toValuationSubring → v.evalAt (x + y) = v.evalAt x + v.evalAt y := by
    intro x y hx hy
    have h0 : (0 : modularFunctionFieldBar N) ∈ v.toValuationSubring := zero_mem _
    rw [show x + y = x - (0 - y) by ring, GaussReduction.evalAt_sub_of_mem v hvrat hx (sub_mem h0 hy),
      GaussReduction.evalAt_sub_of_mem v hvrat h0 hy, hzero]
    ring
  have hsmul : ∀ (c : AlgebraicClosure ℚ) {x : modularFunctionFieldBar N}, x ∈ v.toValuationSubring →
      v.evalAt (c • x) = c * v.evalAt x := by
    intro c x hx
    rw [Algebra.smul_def, GaussReduction.evalAt_mul_of_mem v hvrat (v.algebraMap_mem' c) hx,
      GaussReduction.evalAt_algebraMap_const v hvrat]
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, hzero]
  | insert j T hj ih =>
    have hfT : ∀ i ∈ T, f i ∈ v.toValuationSubring := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsumT : ∑ i ∈ T, a i • f i ∈ v.toValuationSubring :=
      sum_mem fun i hi => smul_mem_valuationSubring v (a i) (hfT i hi)
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hadd (smul_mem_valuationSubring v (a j) (hf j (Finset.mem_insert_self j T))) hsumT,
      hsmul (a j) (hf j (Finset.mem_insert_self j T)), ih hfT]

private def diffQuot (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (u : modularFunctionFieldBar N)
    (j : Fin r) : modularFunctionFieldBar N :=
  (s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹
    - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)) * u⁻¹

private theorem sub_evalVec_mem (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (j : Fin r) :
    s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)
      ∈ P.toValuationSubring ∧
    P.evalAt (s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)) = 0 := by
  have hPrat := isRational N P
  have hymem := mul_inv_pivot_mem hs (basis_mem hs j) P
  have hev : evalVec s P j = P.evalAt (s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹) := by
    unfold evalVec
    rw [dif_pos (pos_of_isEmbBasis hs)]
  refine ⟨sub_mem hymem (P.algebraMap_mem' _), ?_⟩
  rw [GaussReduction.evalAt_sub_of_mem P hPrat hymem (P.algebraMap_mem' _),
    GaussReduction.evalAt_algebraMap_const P hPrat, hev, sub_self]

private theorem diffQuot_mem (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {u : modularFunctionFieldBar N}
    (hu : P.ord u = 1) (j : Fin r) : diffQuot hs P u j ∈ P.toValuationSubring := by
  have hPrat := isRational N P
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hu
    exact zero_ne_one hu
  obtain ⟨hdmem, hd0⟩ := sub_evalVec_mem hs P j
  unfold diffQuot
  by_cases hd : s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j) = 0
  · rw [hd, zero_mul]
    exact zero_mem _
  refine GaussReduction.mem_of_ord_nonneg_gen P (mul_ne_zero hd (inv_ne_zero hu0)) ?_
  rw [P.ord_mul hd (inv_ne_zero hu0), P.ord_inv, hu]
  have hge := GaussReduction.ord_nonneg_of_mem_gen P hdmem hd
  have hne : P.ord (s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)) ≠ 0 := fun h0 =>
    StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero P hPrat hd h0 hd0
  omega

set_option maxHeartbeats 1600000 in

private theorem regVal_chord_eq (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {u : modularFunctionFieldBar N} (hu : P.ord u = 1) (q : Fin r × Fin r) :
    regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
      = evalVec s P q.1 * P.evalAt (diffQuot hs P u q.2) - evalVec s P q.2 * P.evalAt (diffQuot hs P u q.1) := by
  have hPrat := isRational N P
  unfold regVal
  rw [dif_pos (pos_of_isEmbBasis hs), pow_one, pow_one]
  have hid : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
        * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹
      = evalVec s P q.1 • diffQuot hs P u q.2 - evalVec s P q.2 • diffQuot hs P u q.1 := by
    unfold diffQuot
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring
  rw [hid, GaussReduction.evalAt_sub_of_mem P hPrat (smul_mem_valuationSubring P _ (diffQuot_mem hs P hu _))
      (smul_mem_valuationSubring P _ (diffQuot_mem hs P hu _)),
    Algebra.smul_def, Algebra.smul_def,
    GaussReduction.evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) (diffQuot_mem hs P hu _),
    GaussReduction.evalAt_mul_of_mem P hPrat (P.algebraMap_mem' _) (diffQuot_mem hs P hu _),
    GaussReduction.evalAt_algebraMap_const P hPrat, GaussReduction.evalAt_algebraMap_const P hPrat]

set_option maxHeartbeats 1600000 in

private theorem sum_smul_mul_eq_sum_smul_diffQuot (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (u : modularFunctionFieldBar N) (a : Fin r → AlgebraicClosure ℚ) (hP0 : ∑ j, a j * evalVec s P j = 0) :
    (∑ j, a j • s j) * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹
      = ∑ j, a j • diffQuot hs P u j := by
  have hconst : ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j)
      * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j) = 0 := by
    have h : ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j)
        * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (∑ j, a j * evalVec s P j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
    rw [h, hP0, map_zero]
  simp only [Algebra.smul_def]
  unfold diffQuot
  rw [Finset.sum_mul, Finset.sum_mul]
  symm
  calc ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j)
        * ((s j * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)) * u⁻¹)
      = ∑ j, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j) * s j
            * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j)
            * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j) * u⁻¹) :=
        Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j) * s j
            * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹
          - (∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j)
            * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s P j)) * u⁻¹ := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a j) * s j
            * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹ := by
        rw [hconst, zero_mul, sub_zero]

set_option maxHeartbeats 1600000 in

private theorem exists_sum_mul_evalVec_eq_zero_ne (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {u : modularFunctionFieldBar N} (hu : P.ord u = 1) :
    ∃ a : Fin r → AlgebraicClosure ℚ, ∑ j, a j * evalVec s P j = 0 ∧
      ∑ j, a j * P.evalAt (diffQuot hs P u j) ≠ 0 := by
  classical
  have hPrat := isRational N P
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hu
    exact zero_ne_one hu
  have hk0 : s (pivotIndex s P (pos_of_isEmbBasis hs)) ≠ 0 := hs.1.ne_zero _

  obtain ⟨u₂, hu₂, hu₂n⟩ := exists_mem_notMem_sub_single N (embDivisor N - Finsupp.single P (1 : ℤ)) P
    (le_of_eq (degree_embDivisor_sub_sub N P P).symm)
  have hu₂E : u₂ ∈ riemannRochSpace (embDivisor N) :=
    riemannRochSpace_mono (sub_le_self _ (Finsupp.single_nonneg.mpr zero_le_one)) hu₂
  obtain ⟨hu₂0, hord₂⟩ := ord_eq_of_mem_of_notMem hu₂ hu₂n
  rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at hord₂
  obtain ⟨a, hau⟩ : ∃ a : Fin r → AlgebraicClosure ℚ, ∑ j, a j • s j = u₂ := by
    have h : u₂ ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by rw [hs.2]; exact hu₂E
    exact (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp h

  have hP0 : ∑ j, a j * evalVec s P j = 0 := by
    rw [← evalAt_sum_smul_mul_inv_pivot hs P a, hau]
    apply StandardAnnulus.evalAt_eq_zero_of_ord_pos P (mul_ne_zero hu₂0 (inv_ne_zero hk0))
    rw [P.ord_mul hu₂0 (inv_ne_zero hk0), P.ord_inv, ord_pivot_eq hs P, hord₂]
    omega
  refine ⟨a, hP0, ?_⟩

  have hne : u₂ * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hu₂0 (inv_ne_zero hk0)) (inv_ne_zero hu0)
  have hw0 : P.evalAt (u₂ * (s (pivotIndex s P (pos_of_isEmbBasis hs)))⁻¹ * u⁻¹) ≠ 0 := by
    apply StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero P hPrat hne
    rw [P.ord_mul (mul_ne_zero hu₂0 (inv_ne_zero hk0)) (inv_ne_zero hu0),
      P.ord_mul hu₂0 (inv_ne_zero hk0), P.ord_inv, P.ord_inv, ord_pivot_eq hs P, hord₂, hu]
    omega
  rw [← hau, sum_smul_mul_eq_sum_smul_diffQuot hs P u a hP0,
    evalAt_sum_smul_of_mem P Finset.univ a (diffQuot hs P u) (fun j _ => diffQuot_mem hs P hu j)] at hw0
  exact hw0

private theorem exists_regVal_chord_ne_zero (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {u : modularFunctionFieldBar N} (hu : P.ord u = 1) :
    ∃ q : Fin r × Fin r, regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1) ≠ 0 := by
  classical
  have hr := pos_of_isEmbBasis hs
  obtain ⟨a, hP0, hne⟩ := exists_sum_mul_evalVec_eq_zero_ne hs P hu
  by_contra hall
  push Not at hall
  apply hne

  have hprop : ∀ j, P.evalAt (diffQuot hs P u j)
      = evalVec s P j * P.evalAt (diffQuot hs P u (pivotIndex s P hr)) := by
    intro j
    have h := hall (pivotIndex s P hr, j)
    rw [regVal_chord_eq hs P hu] at h
    simp only at h
    rw [show evalVec s P (pivotIndex s P hr) = 1 from evalVec_pivot hs P, one_mul, sub_eq_zero] at h
    exact h
  calc ∑ j, a j * P.evalAt (diffQuot hs P u j)
      = (∑ j, a j * evalVec s P j) * P.evalAt (diffQuot hs P u (pivotIndex s P hr)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by rw [hprop j]; ring
    _ = 0 := by rw [hP0, zero_mul]

end EmbSeparation
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.ModularCurve"

noncomputable section

namespace HarmonicGlue

private noncomputable def ballSubring {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) :
    ValuationSubring K where
  carrier := {x | μ x ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul]
    exact mul_le_one₀ ha (μ.nonneg b) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact (hμ a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rwa [map_neg_eq_map]
  mem_or_inv_mem' := by
    intro x
    simp only [Set.mem_setOf_eq]
    by_cases hx : μ x ≤ 1
    · exact Or.inl hx
    · right
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hx))

private theorem exists_valuationSubring_ball (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (hμ : IsNonarchimedean μ) (p : ℕ) (hp : p.Prime) (hμp : μ (p : AlgebraicClosure ℚ) < 1) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), (∀ y, y ∈ A ↔ μ y ≤ 1) ∧ A.LiesOverPrime p := by
  have _ := hp
  refine ⟨ballSubring μ hμ, fun y => Iff.rfl, ?_⟩
  show ((p : ℕ) : AlgebraicClosure ℚ) ∈ (ballSubring μ hμ).nonunits
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases hp0 : ((p : ℕ) : AlgebraicClosure ℚ) = 0
  · exact Or.inl hp0
  · right
    change ¬ (μ ((p : ℕ) : AlgebraicClosure ℚ)⁻¹ ≤ 1)
    rw [map_inv₀, not_le]
    exact one_lt_inv_iff₀.mpr ⟨(μ.pos (by exact_mod_cast hp0)), hμp⟩

section Kernel

open AlgebraicCurve.ReductionGraph

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}

private def cfun (Γ : AdaptedCovering pf A F P₀ p s μ) (f : F) : ℝ :=
  Γ.cuspChart.logGaussNorm μ f

open Classical in

private def localTerm (Γ : AdaptedCovering pf A F P₀ p s μ) (P Q : Place (AlgebraicClosure ℚ) F) : ℝ :=
  if h : ∃ i, P ∈ (Γ.chart i).dom ∧ Q ∈ (Γ.chart i).dom then
    if (Γ.chart h.choose).placeMap P = (Γ.chart h.choose).placeMap Q then
      -Real.log (μ (P.evalAt (Γ.T h.choose ((Γ.chart h.choose).placeMap P))
        - Q.evalAt (Γ.T h.choose ((Γ.chart h.choose).placeMap P))))
    else 0
  else if h' : ∃ e, P ∈ (Γ.an e).dom ∧ Q ∈ (Γ.an e).dom then
    -Real.log (μ (P.evalAt (Γ.an h'.choose).param - Q.evalAt (Γ.an h'.choose).param))
      - (-Real.log (μ (P.evalAt (Γ.an h'.choose).param)))
          * (-Real.log (μ (Q.evalAt (Γ.an h'.choose).param))) / Γ.len h'.choose
  else 0

private def nearKernel (Γ : AdaptedCovering pf A F P₀ p s μ) (P Q : Place (AlgebraicClosure ℚ) F) : ℝ :=
  pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx)
      (Γ.retract P) (Γ.retract Q)
    + localTerm Γ P Q

private def kernel (Γ : AdaptedCovering pf A F P₀ p s μ) (P Q : Place (AlgebraicClosure ℚ) F) : ℝ :=
  gluedKernel Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx) Γ.retract
    (nearKernel Γ) P Q

private theorem cfun_mul (Γ : AdaptedCovering pf A F P₀ p s μ) {f₁ f₂ : F} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0) :
    cfun Γ (f₁ * f₂) = cfun Γ f₁ + cfun Γ f₂ :=
  Γ.logGaussNorm_cuspChart_mul h₁ h₂

private theorem cfun_add_le (Γ : AdaptedCovering pf A F P₀ p s μ) {f₁ f₂ : F} (h₁ : f₁ ≠ 0) (h₂ : f₂ ≠ 0)
    (h₁₂ : f₁ + f₂ ≠ 0) : cfun Γ (f₁ + f₂) ≤ max (cfun Γ f₁) (cfun Γ f₂) :=
  Γ.cuspChart.logGaussNorm_add_le μ Γ.ball h₁ h₂ h₁₂

private theorem abs_cfun_le (Γ : AdaptedCovering pf A F P₀ p s μ) (hp : 0 < μ p) (l : Fin r) :
    |cfun Γ (s l)| ≤ pf.B * (-Real.log (μ p)) :=
  Γ.abs_logGaussNorm_cuspChart_le hp l

end Kernel
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

section Green

open AlgebraicCurve.ReductionGraph

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}

private theorem localTerm_eq_zero_of_piece_ne (Γ : AdaptedCovering pf A F P₀ p s μ)
    {P Q : Place (AlgebraicClosure ℚ) F} (h : piece (Γ.retract P) ≠ piece (Γ.retract Q)) :
    localTerm Γ P Q = 0 := by
  have h1 : ¬ ∃ i, P ∈ (Γ.chart i).dom ∧ Q ∈ (Γ.chart i).dom := by
    rintro ⟨i, hP, hQ⟩
    exact h (by rw [Γ.retract_of_mem_chart hP, Γ.retract_of_mem_chart hQ])
  have h2 : ¬ ∃ e, P ∈ (Γ.an e).dom ∧ Q ∈ (Γ.an e).dom := by
    rintro ⟨e, hP, hQ⟩
    exact h (by rw [Γ.retract_of_mem_an hP, Γ.retract_of_mem_an hQ, piece_inr, piece_inr])
  unfold localTerm
  rw [dif_neg h1, dif_neg h2]

private theorem kernel_eq (Γ : AdaptedCovering pf A F P₀ p s μ) (P Q : Place (AlgebraicClosure ℚ) F) :
    kernel Γ P Q = pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx)
      (Γ.retract P) (Γ.retract Q) + localTerm Γ P Q := by
  unfold kernel gluedKernel
  split_ifs with h
  · rfl
  · rw [localTerm_eq_zero_of_piece_ne Γ h, add_zero]

open Classical in

private theorem localTerm_of_mem_chart (Γ : AdaptedCovering pf A F P₀ p s μ)
    {P Q : Place (AlgebraicClosure ℚ) F} {i : Fin pf.n} (hP : P ∈ (Γ.chart i).dom) :
    localTerm Γ P Q = if Q ∈ (Γ.chart i).dom ∧ (Γ.chart i).placeMap Q = (Γ.chart i).placeMap P then
      -Real.log (μ (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))
        - Q.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) else 0 := by
  unfold localTerm
  by_cases hQ : Q ∈ (Γ.chart i).dom
  · have h : ∃ j, P ∈ (Γ.chart j).dom ∧ Q ∈ (Γ.chart j).dom := ⟨i, hP, hQ⟩
    have hi : h.choose = i := Γ.chart_unique P i h.choose hP h.choose_spec.1
    rw [dif_pos h]
    have key : ∀ j, j = i →
        (if (Γ.chart j).placeMap P = (Γ.chart j).placeMap Q then
          -Real.log (μ (P.evalAt (Γ.T j ((Γ.chart j).placeMap P))
            - Q.evalAt (Γ.T j ((Γ.chart j).placeMap P)))) else 0)
        = if Q ∈ (Γ.chart i).dom ∧ (Γ.chart i).placeMap Q = (Γ.chart i).placeMap P then
            -Real.log (μ (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))
              - Q.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) else 0 := by
      rintro j rfl
      by_cases hm : (Γ.chart j).placeMap Q = (Γ.chart j).placeMap P
      · rw [if_pos hm.symm, if_pos ⟨hQ, hm⟩]
      · rw [if_neg (fun h' => hm h'.symm), if_neg (fun h' => hm h'.2)]
    exact key _ hi
  · have h1 : ¬ ∃ j, P ∈ (Γ.chart j).dom ∧ Q ∈ (Γ.chart j).dom := by
      rintro ⟨j, hPj, hQj⟩
      have hji : j = i := Γ.chart_unique P i j hP hPj
      subst hji
      exact hQ hQj
    have h2 : ¬ ∃ e, P ∈ (Γ.an e).dom ∧ Q ∈ (Γ.an e).dom := fun ⟨e, hPe, _⟩ =>
      Γ.chart_an_disjoint P i e hP hPe
    rw [dif_neg h1, dif_neg h2, if_neg (fun h' => hQ h'.1)]

open Classical in

private theorem localTerm_of_mem_an (Γ : AdaptedCovering pf A F P₀ p s μ)
    {P Q : Place (AlgebraicClosure ℚ) F} {e : Fin pf.m} (hP : P ∈ (Γ.an e).dom) :
    localTerm Γ P Q = if Q ∈ (Γ.an e).dom then
      -Real.log (μ (P.evalAt (Γ.an e).param - Q.evalAt (Γ.an e).param))
        - (-Real.log (μ (P.evalAt (Γ.an e).param)))
            * (-Real.log (μ (Q.evalAt (Γ.an e).param))) / Γ.len e
      else 0 := by
  unfold localTerm
  have h1 : ¬ ∃ j, P ∈ (Γ.chart j).dom ∧ Q ∈ (Γ.chart j).dom := fun ⟨j, hPj, _⟩ =>
    Γ.chart_an_disjoint P j e hPj hP
  rw [dif_neg h1]
  by_cases hQ : Q ∈ (Γ.an e).dom
  · have h : ∃ e', P ∈ (Γ.an e').dom ∧ Q ∈ (Γ.an e').dom := ⟨e, hP, hQ⟩
    have he : h.choose = e := Γ.an_unique P e h.choose hP h.choose_spec.1
    rw [dif_pos h, if_pos hQ, he]
  · have h2 : ¬ ∃ e', P ∈ (Γ.an e').dom ∧ Q ∈ (Γ.an e').dom := by
      rintro ⟨e', hPe', hQe'⟩
      have hee : e' = e := Γ.an_unique P e e' hP hPe'
      subst hee
      exact hQ hQe'
    rw [dif_neg h2, if_neg hQ]

private theorem logGaussNorm_cusp_sub_eq_sum (Γ : AdaptedCovering pf A F P₀ p s μ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) F] {f : F} (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ w, D w = w.ord f) (i : Fin pf.n) :
    (Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart i).logGaussNorm μ f
      = ∑ u, (D.sum fun w n => (n : ℝ) * vertexWeight Γ.src Γ.tgt Γ.len (Γ.retract w) u)
          * groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i u := by
  have h1 := Γ.isGrounded_logGaussNorm hf D hD
  have h2 := isGrounded_sum_mul_groundPotential Γ.src Γ.tgt Γ.len Γ.connected_adjGraph Γ.len_pos
    Γ.cuspIdx (fun v => D.sum fun w n => (n : ℝ) * vertexWeight Γ.src Γ.tgt Γ.len (Γ.retract w) v)
  have h3 := congrFun (h1.unique Γ.connected_adjGraph Γ.len_pos h2) i
  exact h3

private theorem sum_mul_pairPotential_inl (Γ : AdaptedCovering pf A F P₀ p s μ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) F] {f : F} (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ w, D w = w.ord f) (i : Fin pf.n) :
    ∑ w ∈ D.support, (D w : ℝ) * pairPotential Γ.src Γ.tgt Γ.len
        (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx) (Sum.inl i) (Γ.retract w)
      = (Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart i).logGaussNorm μ f := by
  rw [logGaussNorm_cusp_sub_eq_sum Γ hf D hD i]
  simp only [pairPotential_inl_left, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

open Classical AlgebraicCurve.ReductionGraph in

private theorem sum_erase_mul_kernel_disc (Γ : AdaptedCovering pf A F P₀ p s μ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) F] {P : Place (AlgebraicClosure ℚ) F} {i : Fin pf.n}
    (hPi : P ∈ (Γ.chart i).dom) (D : Divisor (AlgebraicClosure ℚ) F)
    (hD : ∀ w, D w = w.ord ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))))) :
    ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
      = cfun Γ ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) - groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i := by
  obtain ⟨hu, hres, hord1, hpos, hsep⟩ := Γ.disc i P hPi
  have hu0 : ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) ≠ 0 := (Γ.chart i).coe_ne_zero_of_residue_ne_zero hres
  have hDP : D P = 1 := by
    rw [hD P]
    exact (Γ.chart i).ord_eq_one_of_disc hPi hu hres hord1 hpos hsep

  have h1u : (1 : AlgebraicClosure ℚ) • ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) ∈ (Γ.chart i).integers := by
    rw [one_smul]
    exact hu
  have h1res : (Γ.chart i).residue ⟨(1 : AlgebraicClosure ℚ) • ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))), h1u⟩ ≠ 0 := by
    have h1 : (⟨(1 : AlgebraicClosure ℚ) • ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))), h1u⟩ : (Γ.chart i).integers) = ⟨((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))), hu⟩ :=
      Subtype.ext (one_smul _ _)
    rw [h1]
    exact hres
  have hG : (Γ.chart i).logGaussNorm μ ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) = 0 := by
    rw [(Γ.chart i).logGaussNorm_eq_neg_log μ Γ.ball h1u h1res, map_one, Real.log_one, neg_zero]

  have hdiag : kernel Γ P P = groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i := by
    rw [kernel_eq, Γ.retract_of_mem_chart hPi, pairPotential_inl_inl, localTerm_of_mem_chart Γ hPi,
      if_pos ⟨hPi, rfl⟩, sub_self, map_zero, Real.log_zero, neg_zero, add_zero]

  have hfull : (D.sum fun w n => (n : ℝ) * kernel Γ P w) = cfun Γ ((Γ.T i ((Γ.chart i).placeMap P)) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) := by
    have hps := sum_mul_pairPotential_inl Γ hu0 D hD i
    unfold Finsupp.sum
    simp only [kernel_eq, Γ.retract_of_mem_chart hPi, localTerm_of_mem_chart Γ hPi, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [← Finset.sum_filter]
    rw [hps, hG, sub_zero]
    have hloc : ∑ w ∈ D.support.filter (fun w => w ∈ (Γ.chart i).dom
        ∧ (Γ.chart i).placeMap w = (Γ.chart i).placeMap P),
        (D w : ℝ) * (-Real.log (μ (P.evalAt (Γ.T i ((Γ.chart i).placeMap P)) - w.evalAt (Γ.T i ((Γ.chart i).placeMap P))))) = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [Finset.mem_filter, Finsupp.mem_support_iff] at hw
      by_cases hwP : w = P
      · rw [hwP, sub_self, map_zero, Real.log_zero, neg_zero, mul_zero]
      · exact absurd (by rw [hD w]; exact hsep w hw.2.1 hw.2.2 hwP) hw.1
    rw [hloc, add_zero]
    rfl

  have hsplit : (D.sum fun w n => (n : ℝ) * kernel Γ P w)
      = ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) + (D P : ℝ) * kernel Γ P P := by
    conv_lhs => rw [← Finsupp.erase_add_single P D]
    rw [Finsupp.sum_add_index' (fun w => by simp) (fun w b₁ b₂ => by push_cast; ring),
      Finsupp.sum_single_index (by simp)]
  rw [hsplit, hdiag, hDP] at hfull
  push_cast at hfull
  linarith

end Green
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

set_option maxHeartbeats 1600000 in
open Classical AlgebraicCurve.ReductionGraph in

private theorem kernel_green (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (_hs : IsEmbBasis N s) (p : ℕ) (_hp : p.Prime)
    (pf : CoveringProfile) (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime p)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (_hμ : IsNonarchimedean μ)
    (_hball : ∀ y, y ∈ A ↔ μ y ≤ 1) (_hμp : μ (p : AlgebraicClosure ℚ) < 1)
    (Γ : AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
      (p : AlgebraicClosure ℚ) s μ)
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ w, D w = w.ord f)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hP : D P = 0) :
    (D.sum fun w n => (n : ℝ) * kernel Γ P w) = -Real.log (μ (P.evalAt f)) + cfun Γ f := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hrat : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational := fun w =>
    OfTopTransport.isRational_of_deg_eq_one w (deg_eq_one_modularFunctionFieldBar N w)
  rcases Γ.partition P with ⟨i, hPi, -, -⟩ | ⟨e, hPe, -, -⟩
  ·
    have hT : ∀ w ∈ (Γ.chart i).dom, (Γ.chart i).placeMap w = (Γ.chart i).placeMap P →
        ∃ h : Γ.T i ((Γ.chart i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (w.evalAt (Γ.T i ((Γ.chart i).placeMap P))) ∈ (Γ.chart i).integers,
          (Γ.chart i).residue ⟨_, h⟩ ≠ 0 ∧
          ((Γ.chart i).placeMap w).ord ((Γ.chart i).residue ⟨_, h⟩) = 1 ∧
          0 < w.ord (Γ.T i ((Γ.chart i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (w.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) ∧
          ∀ Q ∈ (Γ.chart i).dom, (Γ.chart i).placeMap Q = (Γ.chart i).placeMap w → Q ≠ w →
            Q.ord (Γ.T i ((Γ.chart i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                  (w.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) = 0 := by
      intro w hw hmap
      have h := Γ.disc i w hw
      have hTT : Γ.T i ((Γ.chart i).placeMap w) = Γ.T i ((Γ.chart i).placeMap P) := by rw [hmap]
      rw [hTT] at h
      exact h
    have hPJ := (Γ.chart i).neg_log_abv_evalAt_eq_of_disc μ Γ.ball (fun w _ => hrat w) hPi hf D hD
      hP (Γ.T i ((Γ.chart i).placeMap P)) hT
    have hps := sum_mul_pairPotential_inl Γ hf D hD i
    unfold Finsupp.sum
    simp only [kernel_eq, Γ.retract_of_mem_chart hPi, localTerm_of_mem_chart Γ hPi, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [← Finset.sum_filter]
    rw [hps, hPJ]
    show _ = _ + (Γ.chart Γ.cuspIdx).logGaussNorm μ f
    ring
  ·
    obtain ⟨c, hc, hcres⟩ := (Γ.chart (Γ.src e)).exists_smul_mem f hf
    obtain ⟨c', hc', hc'res⟩ := (Γ.chart (Γ.tgt e)).exists_smul_mem f hf
    have hGs := (Γ.chart (Γ.src e)).logGaussNorm_eq_neg_log μ Γ.ball hc hcres
    have hGt := (Γ.chart (Γ.tgt e)).logGaussNorm_eq_neg_log μ Γ.ball hc' hc'res
    have hEND := (Γ.attached e).1.neg_log_abv_evalAt_eq μ Γ.ball hf D hD hc hcres hPe hP
    have hdiff := (Γ.end_slopes e hf D hD hc hcres hc' hc'res).2
    have hSLV : ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (Γ.len e - (-Real.log (μ (w.evalAt (Γ.an e).param))))
        = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ)) * Γ.len e - ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (-Real.log (μ (w.evalAt (Γ.an e).param))) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hℓ : Γ.len e ≠ 0 := (Γ.len_pos e).ne'
    have hu : Γ.len e * (Γ.len e)⁻¹ = 1 := mul_inv_cancel₀ hℓ
    have hps := sum_mul_pairPotential_inl Γ hf D hD (Γ.src e)
    have hpt := sum_mul_pairPotential_inl Γ hf D hD (Γ.tgt e)
    have hA : ∑ w ∈ D.support, (D w : ℝ) * ((Γ.len e - (-Real.log (μ (P.evalAt (Γ.an e).param)))) / Γ.len e
        * pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx) (Sum.inl (Γ.src e)) (Γ.retract w))
        = (Γ.len e - (-Real.log (μ (P.evalAt (Γ.an e).param)))) / Γ.len e
          * ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f) := by
      rw [← hps, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hB : ∑ w ∈ D.support, (D w : ℝ) * ((-Real.log (μ (P.evalAt (Γ.an e).param))) / Γ.len e
        * pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx) (Sum.inl (Γ.tgt e)) (Γ.retract w))
        = (-Real.log (μ (P.evalAt (Γ.an e).param))) / Γ.len e
          * ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.tgt e)).logGaussNorm μ f) := by
      rw [← hpt, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hloc : ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * ((-Real.log (μ (P.evalAt (Γ.an e).param - w.evalAt (Γ.an e).param))) - (-Real.log (μ (P.evalAt (Γ.an e).param))) * (-Real.log (μ (w.evalAt (Γ.an e).param))) / Γ.len e)
        = (∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (-Real.log (μ (P.evalAt (Γ.an e).param - w.evalAt (Γ.an e).param))))
          - (-Real.log (μ (P.evalAt (Γ.an e).param))) / Γ.len e * ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ) * (-Real.log (μ (w.evalAt (Γ.an e).param))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    unfold Finsupp.sum
    simp only [kernel_eq, Γ.retract_of_mem_an hPe, pairPotential_inr_left, localTerm_of_mem_an Γ hPe,
      mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [← Finset.sum_filter]
    rw [hA, hB, hloc]
    show _ = _ + (Γ.chart Γ.cuspIdx).logGaussNorm μ f
    linear_combination (-1 : ℝ) * hEND
      + ((-Real.log (μ (P.evalAt (Γ.an e).param))) * (Γ.len e)⁻¹ - 1) * hGs
      + (-((-Real.log (μ (P.evalAt (Γ.an e).param))) * (Γ.len e)⁻¹)) * hGt
      + (-((-Real.log (μ (P.evalAt (Γ.an e).param))) * (Γ.len e)⁻¹)) * hdiff
      + (-((-Real.log (μ (P.evalAt (Γ.an e).param))) * (Γ.len e)⁻¹)) * hSLV
      + ((Γ.chart Γ.cuspIdx).logGaussNorm μ f - (Γ.chart (Γ.src e)).logGaussNorm μ f
          + (-Real.log (μ (P.evalAt (Γ.an e).param))) * ((((Γ.xs e).ord ((Γ.chart (Γ.src e)).residue ⟨c • f, hc⟩) : ℤ) : ℝ)
            - ∑ w ∈ D.support.filter (· ∈ (Γ.an e).dom), (D w : ℝ))) * hu

private theorem _root_.HarmonicGlue.exists_evalVec_mul_ne_of_ne (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    {P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hPQ : P ≠ Q) :
    ∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i :=
  AlgebraicCurve.EmbSeparation.exists_evalVec_mul_ne_of_ne hs hPQ

p2m_export "HarmonicGlue" "exists_evalVec_mul_ne_of_ne"

private theorem _root_.HarmonicGlue.exists_regVal_chord_ne_zero (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) {u : modularFunctionFieldBar N}
    (hu : P.ord u = 1) :
    ∃ q : Fin r × Fin r, regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1) ≠ 0 :=
  AlgebraicCurve.EmbSeparation.exists_regVal_chord_ne_zero hs P hu

p2m_export "HarmonicGlue" "exists_regVal_chord_ne_zero"
set_option maxHeartbeats 1600000 in
open AlgebraicCurve.ReductionGraph in

private theorem exists_const_abs_kernel_sub_prox_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (pf : CoveringProfile) :
    ∃ C : ℝ, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean μ →
        (∀ y, y ∈ A ↔ μ y ≤ 1) → μ (p : AlgebraicClosure ℚ) < 1 →
        ∀ Γ : AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
          (p : AlgebraicClosure ℚ) s μ,
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
          |kernel Γ P Q - prox μ (evalVec s P) (evalVec s Q)|
            ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  refine ⟨(pf.m : ℝ) * (pf.k : ℝ) + |pf.Cc| + (pf.k : ℝ) + |pf.Cc| * (pf.k : ℝ), ?_⟩
  intro A hA μ hμ hball hμp Γ P Q hPQ
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hμp0 : μ (p : AlgebraicClosure ℚ) ≠ 0 := μ.ne_zero hp0
  have hμpos : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hlam : 0 ≤ (-Real.log (μ (p : AlgebraicClosure ℚ))) := neg_nonneg.mpr (Real.log_nonpos hμpos.le hμp.le)
  have hsep := exists_evalVec_mul_ne_of_ne N s hs hPQ
  have hmk : (0 : ℝ) ≤ (pf.m : ℝ) * (pf.k : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ (pf.k : ℝ) := by positivity
  have hR := abs_groundPotential_le Γ.src Γ.tgt Γ.len Γ.connected_adjGraph Γ.len_pos Γ.cuspIdx
  have hRle := Γ.sum_len_le hμp0
  have hf1 : 0 ≤ (pf.k : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := mul_nonneg hk hlam
  have hf2 : 0 ≤ |pf.Cc| * (pf.k : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := mul_nonneg (mul_nonneg (abs_nonneg _) hk) hlam
  have hf3 : pf.Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))) ≤ |pf.Cc| * (-Real.log (μ (p : AlgebraicClosure ℚ))) := mul_le_mul_of_nonneg_right (le_abs_self _) hlam
  have hf4 : 0 ≤ |pf.Cc| * (-Real.log (μ (p : AlgebraicClosure ℚ))) := mul_nonneg (abs_nonneg _) hlam

  have hcross : ∀ (h : (∃ i, P ∈ (Γ.chart i).dom ∧ Q ∉ (Γ.chart i).dom) ∨
      (∃ e, P ∈ (Γ.an e).dom ∧ Q ∉ (Γ.an e).dom)),
      |kernel Γ P Q - prox μ (evalVec s P) (evalVec s Q)|
        ≤ ((pf.m : ℝ) * (pf.k : ℝ) + |pf.Cc| + (pf.k : ℝ) + |pf.Cc| * (pf.k : ℝ)) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro h
    have h1 := Γ.abs_gluedKernel_sub_prox_le hμp0 (nearKernel Γ) h
    calc |kernel Γ P Q - prox μ (evalVec s P) (evalVec s Q)|
        ≤ ((pf.m : ℝ) * (pf.k : ℝ) + pf.Cc) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := h1
      _ ≤ ((pf.m : ℝ) * (pf.k : ℝ) + |pf.Cc| + (pf.k : ℝ) + |pf.Cc| * (pf.k : ℝ)) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
          linarith
  rcases Γ.partition P with ⟨i, hPi, -, -⟩ | ⟨e, hPe, -, -⟩
  · by_cases hQi : Q ∈ (Γ.chart i).dom
    ·
      have hJ := hR i i
      have hcmp := Γ.chartCmp i P hPi Q hQi hPQ hsep
      rw [kernel_eq, Γ.retract_of_mem_chart hPi, Γ.retract_of_mem_chart hQi, pairPotential_inl_inl,
        localTerm_of_mem_chart Γ hPi]
      by_cases hfib : (Γ.chart i).placeMap Q = (Γ.chart i).placeMap P
      · rw [if_pos ⟨hQi, hfib⟩]
        have h2 := hcmp.1 hfib.symm
        calc |groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i
              + -Real.log (μ (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))
                  - Q.evalAt (Γ.T i ((Γ.chart i).placeMap P))))
              - prox μ (evalVec s P) (evalVec s Q)|
            = |groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i
              + -(prox μ (evalVec s P) (evalVec s Q)
                  + Real.log (μ (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))
                      - Q.evalAt (Γ.T i ((Γ.chart i).placeMap P)))))| := by
              congr 1
              ring
          _ ≤ |groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i|
              + |-(prox μ (evalVec s P) (evalVec s Q)
                  + Real.log (μ (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))
                      - Q.evalAt (Γ.T i ((Γ.chart i).placeMap P)))))| := abs_add_le _ _
          _ ≤ (∑ e, Γ.len e) + pf.Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
              rw [abs_neg]
              exact add_le_add hJ h2
          _ ≤ ((pf.m : ℝ) * (pf.k : ℝ) + |pf.Cc| + (pf.k : ℝ) + |pf.Cc| * (pf.k : ℝ)) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
              linarith
      · rw [if_neg (fun h => hfib h.2), add_zero]
        have h2 := hcmp.2 (fun h => hfib h.symm)
        calc |groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i - prox μ (evalVec s P) (evalVec s Q)|
            ≤ |groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i| + |prox μ (evalVec s P) (evalVec s Q)| :=
              abs_sub _ _
          _ ≤ (∑ e, Γ.len e) + pf.Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))) := add_le_add hJ h2
          _ ≤ ((pf.m : ℝ) * (pf.k : ℝ) + |pf.Cc| + (pf.k : ℝ) + |pf.Cc| * (pf.k : ℝ)) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
              linarith
    · exact hcross (Or.inl ⟨i, hPi, hQi⟩)
  · by_cases hQe : Q ∈ (Γ.an e).dom
    ·
      have hpp := abs_pairPotential_le Γ.src Γ.tgt Γ.len
        (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx) hR (Γ.onSkeleton_retract P) (Γ.onSkeleton_retract Q)
      have hskP := Γ.onSkeleton_retract P
      have hskQ := Γ.onSkeleton_retract Q
      rw [Γ.retract_of_mem_an hPe, onSkeleton_inr_iff] at hskP
      rw [Γ.retract_of_mem_an hQe, onSkeleton_inr_iff] at hskQ
      have hℓpos := Γ.len_pos e
      have hℓle := Γ.len_le hμp0 e
      have hcmp := Γ.anCmp e P hPe Q hQe hPQ hsep
      rw [← Γ.len_eq e] at hcmp
      have hCc : 0 ≤ pf.Cc := by
        have h0 : 0 ≤ pf.Cc * Γ.len e := (abs_nonneg _).trans hcmp
        by_contra hneg
        rw [not_le] at hneg
        have h1 := mul_neg_of_neg_of_pos hneg hℓpos
        exact absurd h0 (not_le.mpr h1)
      have hprod : 0 ≤ (-Real.log (μ (P.evalAt (Γ.an e).param)))
          * (-Real.log (μ (Q.evalAt (Γ.an e).param))) / Γ.len e :=
        div_nonneg (mul_nonneg hskP.1 hskQ.1) hℓpos.le
      have hprod' : (-Real.log (μ (P.evalAt (Γ.an e).param)))
          * (-Real.log (μ (Q.evalAt (Γ.an e).param))) / Γ.len e ≤ Γ.len e := by
        rw [div_le_iff₀ hℓpos]
        exact mul_le_mul hskP.2 hskQ.2 hskQ.1 hℓpos.le
      rw [kernel_eq, localTerm_of_mem_an Γ hPe, if_pos hQe]
      calc |pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx)
              (Γ.retract P) (Γ.retract Q)
            + (-Real.log (μ (P.evalAt (Γ.an e).param - Q.evalAt (Γ.an e).param))
              - (-Real.log (μ (P.evalAt (Γ.an e).param)))
                * (-Real.log (μ (Q.evalAt (Γ.an e).param))) / Γ.len e)
            - prox μ (evalVec s P) (evalVec s Q)|
          = |pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx)
              (Γ.retract P) (Γ.retract Q)
            + -((-Real.log (μ (P.evalAt (Γ.an e).param)))
                * (-Real.log (μ (Q.evalAt (Γ.an e).param))) / Γ.len e)
            + -(prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (Γ.an e).param - Q.evalAt (Γ.an e).param)))| := by
              congr 1
              ring
        _ ≤ |pairPotential Γ.src Γ.tgt Γ.len (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx)
              (Γ.retract P) (Γ.retract Q)|
            + |-((-Real.log (μ (P.evalAt (Γ.an e).param)))
                * (-Real.log (μ (Q.evalAt (Γ.an e).param))) / Γ.len e)|
            + |-(prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (Γ.an e).param - Q.evalAt (Γ.an e).param)))| :=
              abs_add_three _ _ _
        _ ≤ (∑ e, Γ.len e) + Γ.len e + pf.Cc * Γ.len e := by
              rw [abs_neg, abs_neg, abs_of_nonneg hprod]
              exact add_le_add (add_le_add hpp hprod') hcmp
        _ ≤ ((pf.m : ℝ) * (pf.k : ℝ) + |pf.Cc| + (pf.k : ℝ) + |pf.Cc| * (pf.k : ℝ)) * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
              rw [abs_of_nonneg hCc]
              have hf5 : pf.Cc * Γ.len e ≤ pf.Cc * ((pf.k : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))) :=
                mul_le_mul_of_nonneg_left hℓle hCc
              have hf6 : 0 ≤ pf.Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))) := mul_nonneg hCc hlam
              linarith
    · exact hcross (Or.inr ⟨e, hPe, hQe⟩)

section FSlot

open IsLocalRing

private theorem abv_add_eq_of_lt {L : Type*} [Field L] (μ : AbsoluteValue L ℝ)
    (hμ : IsNonarchimedean (⇑μ)) {x y : L} (h : μ x < μ y) : μ (x + y) = μ y := by
  have hle : μ (x + y) ≤ μ y := le_trans (hμ x y) (max_le h.le le_rfl)
  refine le_antisymm hle ?_
  have h2 : μ y ≤ max (μ (x + y)) (μ x) := by
    have h3 := hμ (x + y) (-x)
    rw [show x + y + -x = y by ring, μ.map_neg] at h3
    exact h3
  rcases le_max_iff.mp h2 with h4 | h4
  · exact h4
  · exact absurd (lt_of_le_of_lt h4 h) (lt_irrefl _)

private theorem evalAt_zero_aux {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (v : Place L F) (hv : v.IsRational) : v.evalAt (0 : F) = 0 := by
  have h : (0 : F) = 1 - 1 := by ring
  rw [h, GaussReduction.evalAt_sub_of_mem v hv (one_mem _) (one_mem _), sub_self]

private theorem evalAt_ne_zero_of_ord_eq_zero' {L : Type*} [Field L] {F : Type*} [Field F]
    [Algebra L F] (v : Place L F) (hv : v.IsRational) {f : F} (hf : f ≠ 0)
    (h : v.ord f = 0) : v.evalAt f ≠ 0 := by
  have hmem : f ∈ v.toValuationSubring := GaussReduction.mem_of_ord_nonneg_gen v hf h.ge
  have hinv : f⁻¹ ∈ v.toValuationSubring := by
    refine GaussReduction.mem_of_ord_nonneg_gen v (inv_ne_zero hf) ?_
    rw [v.ord_inv, h, neg_zero]
  have h1 : v.evalAt f * v.evalAt f⁻¹ = 1 := by
    rw [← GaussReduction.evalAt_mul_of_mem v hv hmem hinv, mul_inv_cancel₀ hf, v.evalAt_one]
  intro h0
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

private theorem one_le_ord_of_evalAt_eq_zero' {L : Type*} [Field L] {F : Type*} [Field F]
    [Algebra L F] (v : Place L F) (hv : v.IsRational) {f : F} (hf : f ≠ 0)
    (hmem : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 1 ≤ v.ord f := by
  have hnn : 0 ≤ v.ord f := GaussReduction.ord_nonneg_of_mem_gen v hmem hf
  rcases hnn.eq_or_lt with heq | hlt
  · exact absurd h0 (evalAt_ne_zero_of_ord_eq_zero' v hv hf heq.symm)
  · omega

private theorem evalAt_pow_of_mem' {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (v : Place L F) (hv : v.IsRational) {f : F} (hmem : f ∈ v.toValuationSubring) :
    ∀ d : ℕ, v.evalAt (f ^ d) = (v.evalAt f) ^ d := by
  intro d
  induction d with
  | zero => simp [v.evalAt_one]
  | succ d ih =>
    rw [pow_succ, GaussReduction.evalAt_mul_of_mem v hv (pow_mem hmem d) hmem, ih, pow_succ]

private theorem evalAt_smul_sub_smul {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (v : Place L F) (hv : v.IsRational) (a b : L) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (a • f - b • g) = a * v.evalAt f - b * v.evalAt g := by
  have hsf : a • f ∈ v.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' a) hf
  have hsg : b • g ∈ v.toValuationSubring := by
    rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' b) hg
  rw [GaussReduction.evalAt_sub_of_mem v hv hsf hsg]
  congr 1
  · rw [Algebra.smul_def, GaussReduction.evalAt_mul_of_mem v hv (v.algebraMap_mem' a) hf,
      GaussReduction.evalAt_algebraMap_const v hv]
  · rw [Algebra.smul_def, GaussReduction.evalAt_mul_of_mem v hv (v.algebraMap_mem' b) hg,
      GaussReduction.evalAt_algebraMap_const v hv]

private theorem ciSup_mul_const_aux' {i : Type*} [Nonempty i] [Finite i] (f : i → ℝ) (a : ℝ)
    (hf : ∀ j, 0 ≤ f j) (ha : 0 ≤ a) :
    (⨆ j, f j * a) = (⨆ j, f j) * a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [mul_zero, ciSup_const]
  refine le_antisymm
    (Real.iSup_le (fun j => mul_le_mul_of_nonneg_right
        (le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) j) ha)
      (mul_nonneg (Real.iSup_nonneg hf) ha)) ?_
  rw [← le_div_iff₀ ha']
  refine Real.iSup_le (fun j => ?_) (div_nonneg (Real.iSup_nonneg fun j => mul_nonneg (hf j) ha) ha)
  rw [le_div_iff₀ ha']
  exact le_ciSup (f := fun k => f k * a) (Set.Finite.bddAbove (Set.finite_range _)) j

private theorem prox_smul_right' {i : Type*} [Nonempty i] [Finite i] {L : Type*} [Field L]
    (μ : AbsoluteValue L ℝ) (x y : i → L) {c : L} (hc : c ≠ 0)
    (hy : 0 < ⨆ j, μ (y j))
    (hm : 0 < ⨆ q : i × i, μ (x q.1 * y q.2 - x q.2 * y q.1)) :
    prox (⇑μ) x (fun j => c * y j) = prox (⇑μ) x y := by
  have hc0 : (0 : ℝ) < μ c := μ.pos hc
  have h1 : (⨆ j, μ (c * y j)) = (⨆ j, μ (y j)) * μ c := by
    rw [← ciSup_mul_const_aux' (fun j => μ (y j)) (μ c) (fun j => μ.nonneg _) (μ.nonneg _)]
    exact iSup_congr fun j => by rw [map_mul, mul_comm]
  have h2 : (⨆ q : i × i, μ (x q.1 * (c * y q.2) - x q.2 * (c * y q.1)))
      = (⨆ q : i × i, μ (x q.1 * y q.2 - x q.2 * y q.1)) * μ c := by
    rw [← ciSup_mul_const_aux' (fun q : i × i => μ (x q.1 * y q.2 - x q.2 * y q.1)) (μ c)
      (fun q => μ.nonneg _) (μ.nonneg _)]
    refine iSup_congr fun q => ?_
    rw [← map_mul]
    congr 1
    ring
  unfold prox
  rw [h1, h2, Real.log_mul (ne_of_gt hy) (ne_of_gt hc0), Real.log_mul (ne_of_gt hm) (ne_of_gt hc0)]
  ring

private theorem pivot_spec' {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  unfold pivotIndex
  have hex : ∃ k : Fin r, ∀ l : Fin r, v.ord (s k) ≤ v.ord (s l) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    obtain ⟨k, hk⟩ := Finite.exists_min (fun k : Fin r => v.ord (s k))
    exact ⟨k, hk⟩
  rw [dif_pos hex]
  exact hex.choose_spec j

private theorem pivot_ratio_mem' {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (hs0 : ∀ j, s j ≠ 0)
    (j : Fin r) : s j * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring := by
  refine GaussReduction.mem_of_ord_nonneg_gen v (mul_ne_zero (hs0 j) (inv_ne_zero (hs0 _))) ?_
  rw [v.ord_mul (hs0 j) (inv_ne_zero (hs0 _)), v.ord_inv]
  have := pivot_spec' s v hr j
  omega

private theorem evalVec_eq' {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (j : Fin r) :
    evalVec s v j = v.evalAt (s j * (s (pivotIndex s v hr))⁻¹) := by
  unfold evalVec
  rw [dif_pos hr]

private theorem evalVec_pivot' {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (_hv : v.IsRational)
    (hs0 : ∀ j, s j ≠ 0) : evalVec s v (pivotIndex s v hr) = 1 := by
  rw [evalVec_eq' s v hr, mul_inv_cancel₀ (hs0 _), v.evalAt_one]

private theorem mem_maximalIdeal_iff_abv_lt_one' {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) {y : L} (hy : y ∈ A) :
    (⟨y, hy⟩ : A) ∈ maximalIdeal A ↔ μ y < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    rcases lt_or_eq_of_le ((hA y).mp hy) with h | h
    · exact h
    · exfalso
      apply hnu
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0, map_zero] at h
        exact zero_ne_one h
      have hyi : y⁻¹ ∈ A := (hA _).mpr (by rw [map_inv₀, h, inv_one])
      exact ⟨⟨⟨y, hy⟩, ⟨y⁻¹, hyi⟩, Subtype.ext (mul_inv_cancel₀ hy0),
        Subtype.ext (inv_mul_cancel₀ hy0)⟩, rfl⟩
  · intro hlt hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have h3 : y * (b : L) = 1 := by
      have h2 := congrArg (Subtype.val) hb
      push_cast at h2
      exact h2
    have h4 : μ y * μ (b : L) = 1 := by
      rw [← map_mul, h3, map_one]
    have h5 : μ (b : L) ≤ 1 := (hA _).mp (SetLike.coe_mem b)
    nlinarith [μ.nonneg (b : L), μ.nonneg y]

private theorem abv_evalAt_eq_of_fibre' {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar]
    [Algebra (IsLocalRing.ResidueField A) Fbar] [HasPrincipalDivisors L F]
    (C : ComponentChart A F Fbar) (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean (⇑μ))
    (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1) (hrat : ∀ w ∈ C.dom, w.IsRational)
    {P : Place L F} (hP : P ∈ C.dom) (T : F)
    (hdisc : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P →
      ∃ h : T - algebraMap L F (w.evalAt T) ∈ C.integers,
        C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap w).ord (C.residue ⟨_, h⟩) = 1 ∧
        0 < w.ord (T - algebraMap L F (w.evalAt T)) ∧
        ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap w → Q ≠ w →
          Q.ord (T - algebraMap L F (w.evalAt T)) = 0)
    {f : F} (hf : f ≠ 0) (hfP : P.ord f = 0) :
    ∃ ε > 0, ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P →
      Q.evalAt T ≠ P.evalAt T → μ (Q.evalAt T - P.evalAt T) < ε →
      μ (Q.evalAt f) = μ (P.evalAt f) ∧ Q.ord f = 0 := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf
  have hDP : D P = 0 := by rw [hD]; exact hfP
  classical
  set S := D.support.filter (fun w => w ∈ C.dom ∧ C.placeMap w = C.placeMap P) with hS

  have hgap : ∀ w ∈ S, 0 < μ (w.evalAt T - P.evalAt T) := by
    intro w hw
    rw [hS, Finset.mem_filter, Finsupp.mem_support_iff] at hw
    obtain ⟨hw0, hwdom, hwpm⟩ := hw
    have hwP : w ≠ P := by
      intro h
      rw [h, hDP] at hw0
      exact hw0 rfl
    obtain ⟨hTm, hTres, -, -, hTsep⟩ := hdisc P hP rfl
    have hT0 : T - algebraMap L F (P.evalAt T) ≠ 0 := C.coe_ne_zero_of_residue_ne_zero hTres
    have hordw : w.ord (T - algebraMap L F (P.evalAt T)) = 0 := hTsep w hwdom hwpm hwP
    have hmemw : T - algebraMap L F (P.evalAt T) ∈ w.toValuationSubring :=
      GaussReduction.mem_of_ord_nonneg_gen w hT0 hordw.ge
    have hmemT : T ∈ w.toValuationSubring := by
      have h1 : T = (T - algebraMap L F (P.evalAt T)) + algebraMap L F (P.evalAt T) := by ring
      rw [h1]
      exact add_mem hmemw (w.algebraMap_mem' _)
    have hval : w.evalAt (T - algebraMap L F (P.evalAt T)) = w.evalAt T - P.evalAt T := by
      rw [GaussReduction.evalAt_sub_of_mem w (hrat w hwdom) hmemT (w.algebraMap_mem' _),
        GaussReduction.evalAt_algebraMap_const w (hrat w hwdom)]
    have hne : w.evalAt T - P.evalAt T ≠ 0 := by
      rw [← hval]
      exact evalAt_ne_zero_of_ord_eq_zero' w (hrat w hwdom) hT0 hordw
    exact μ.pos hne
  obtain ⟨ε, hε0, hεle⟩ : ∃ ε > 0, ∀ w ∈ S, ε ≤ μ (w.evalAt T - P.evalAt T) := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨1, one_pos, by simp [hSe]⟩
    · refine ⟨S.inf' hSne (fun w => μ (w.evalAt T - P.evalAt T)), ?_,
        fun w hw => Finset.inf'_le _ hw⟩
      exact (Finset.lt_inf'_iff hSne).mpr fun w hw => hgap w hw
  refine ⟨ε, hε0, fun Q hQ hQpm hQne hQlt => ?_⟩

  have hDQ : D Q = 0 := by
    by_contra hDQ0
    have hQS : Q ∈ S := by
      rw [hS, Finset.mem_filter, Finsupp.mem_support_iff]
      exact ⟨hDQ0, hQ, hQpm⟩
    exact absurd hQlt (not_lt.mpr (hεle Q hQS))
  have hordQ : Q.ord f = 0 := by rw [← hD]; exact hDQ
  refine ⟨?_, hordQ⟩

  have hPJP := C.neg_log_abv_evalAt_eq_of_disc μ hA hrat hP hf D hD hDP T hdisc
  have hdiscQ : ∀ w ∈ C.dom, C.placeMap w = C.placeMap Q →
      ∃ h : T - algebraMap L F (w.evalAt T) ∈ C.integers,
        C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap w).ord (C.residue ⟨_, h⟩) = 1 ∧
        0 < w.ord (T - algebraMap L F (w.evalAt T)) ∧
        ∀ Q' ∈ C.dom, C.placeMap Q' = C.placeMap w → Q' ≠ w →
          Q'.ord (T - algebraMap L F (w.evalAt T)) = 0 :=
    fun w hw hwQ => hdisc w hw (hwQ.trans hQpm)
  have hPJQ := C.neg_log_abv_evalAt_eq_of_disc μ hA hrat hQ hf D hD hDQ T hdiscQ
  simp only [hQpm] at hPJQ

  have hterms : ∑ w ∈ S, (D w : ℝ) * (-Real.log (μ (Q.evalAt T - w.evalAt T)))
      = ∑ w ∈ S, (D w : ℝ) * (-Real.log (μ (P.evalAt T - w.evalAt T))) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have h1 : Q.evalAt T - w.evalAt T = (Q.evalAt T - P.evalAt T) + (P.evalAt T - w.evalAt T) := by
      ring
    have h2 : μ (Q.evalAt T - w.evalAt T) = μ (P.evalAt T - w.evalAt T) := by
      rw [h1]
      refine abv_add_eq_of_lt μ hμ ?_
      have h3 : μ (P.evalAt T - w.evalAt T) = μ (w.evalAt T - P.evalAt T) := by
        rw [show P.evalAt T - w.evalAt T = -(w.evalAt T - P.evalAt T) by ring, μ.map_neg]
      rw [h3]
      exact lt_of_lt_of_le hQlt (hεle w hw)
    rw [h2]

  have hfP0 : P.evalAt f ≠ 0 := evalAt_ne_zero_of_ord_eq_zero' P (hrat P hP) hf hfP
  have hfQ0 : Q.evalAt f ≠ 0 := evalAt_ne_zero_of_ord_eq_zero' Q (hrat Q hQ) hf hordQ
  have hlog : Real.log (μ (Q.evalAt f)) = Real.log (μ (P.evalAt f)) := by
    nlinarith [hPJP, hPJQ, hterms]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (μ.pos hfQ0)) (Set.mem_Ioi.mpr (μ.pos hfP0)) hlog

private theorem abv_evalAt_eq_of_level' {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar]
    [Algebra (IsLocalRing.ResidueField A) Fbar] [HasPrincipalDivisors L F]
    {An : Annulus A F} {C : ComponentChart A F Fbar} {x : Place (IsLocalRing.ResidueField A) Fbar}
    (hatt : An.IsAttached C x) (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean (⇑μ))
    (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {P : Place L F} (hP : P ∈ An.dom)
    {f : F} (hf : f ≠ 0) (hfP : P.ord f = 0) :
    ∃ ε > 0, ∀ Q ∈ An.dom, μ (Q.evalAt An.param) = μ (P.evalAt An.param) →
      Q.evalAt An.param ≠ P.evalAt An.param → μ (Q.evalAt An.param - P.evalAt An.param) < ε →
      μ (Q.evalAt f) = μ (P.evalAt f) ∧ Q.ord f = 0 := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf
  have hDP : D P = 0 := by rw [hD]; exact hfP
  classical

  have hinj : ∀ w ∈ An.dom, ∀ w' ∈ An.dom, w.evalAt An.param = w'.evalAt An.param → w = w' := by
    intro w hw w' hw' heq
    obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, m, hmmax, hmod⟩ := An.mem_dom w hw
    obtain ⟨u, hu, huniq⟩ := An.existsUnique_evalAt_eq ⟨w.evalAt An.param, hzA⟩ hzmax hz0
      ⟨m, hmmax, hmod⟩
    rw [huniq w ⟨hw, rfl⟩, huniq w' ⟨hw', heq.symm⟩]
  set S := D.support.filter (· ∈ An.dom) with hS
  have hgap : ∀ w ∈ S, 0 < μ (w.evalAt An.param - P.evalAt An.param) := by
    intro w hw
    rw [hS, Finset.mem_filter, Finsupp.mem_support_iff] at hw
    obtain ⟨hw0, hwdom⟩ := hw
    have hwP : w ≠ P := by
      intro h
      rw [h, hDP] at hw0
      exact hw0 rfl
    have hne : w.evalAt An.param - P.evalAt An.param ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      exact hwP (hinj w hwdom P hP heq)
    exact μ.pos hne
  obtain ⟨ε, hε0, hεle⟩ : ∃ ε > 0, ∀ w ∈ S, ε ≤ μ (w.evalAt An.param - P.evalAt An.param) := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨1, one_pos, by simp [hSe]⟩
    · refine ⟨S.inf' hSne (fun w => μ (w.evalAt An.param - P.evalAt An.param)), ?_,
        fun w hw => Finset.inf'_le _ hw⟩
      exact (Finset.lt_inf'_iff hSne).mpr fun w hw => hgap w hw
  refine ⟨ε, hε0, fun Q hQ hQlev hQne hQlt => ?_⟩
  have hDQ : D Q = 0 := by
    by_contra hDQ0
    have hQS : Q ∈ S := by
      rw [hS, Finset.mem_filter, Finsupp.mem_support_iff]
      exact ⟨hDQ0, hQ⟩
    exact absurd hQlt (not_lt.mpr (hεle Q hQS))
  have hordQ : Q.ord f = 0 := by rw [← hD]; exact hDQ
  refine ⟨?_, hordQ⟩
  obtain ⟨c, hcf, hcres⟩ := C.exists_smul_mem f hf
  have hPJP := hatt.neg_log_abv_evalAt_eq μ hA hf D hD hcf hcres hP hDP
  have hPJQ := hatt.neg_log_abv_evalAt_eq μ hA hf D hD hcf hcres hQ hDQ
  have hterms : ∑ w ∈ D.support.filter (· ∈ An.dom),
        (D w : ℝ) * (-Real.log (μ (Q.evalAt An.param - w.evalAt An.param)))
      = ∑ w ∈ D.support.filter (· ∈ An.dom),
        (D w : ℝ) * (-Real.log (μ (P.evalAt An.param - w.evalAt An.param))) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have h1 : Q.evalAt An.param - w.evalAt An.param
        = (Q.evalAt An.param - P.evalAt An.param) + (P.evalAt An.param - w.evalAt An.param) := by
      ring
    have h2 : μ (Q.evalAt An.param - w.evalAt An.param)
        = μ (P.evalAt An.param - w.evalAt An.param) := by
      rw [h1]
      refine abv_add_eq_of_lt μ hμ ?_
      have h3 : μ (P.evalAt An.param - w.evalAt An.param)
          = μ (w.evalAt An.param - P.evalAt An.param) := by
        rw [show P.evalAt An.param - w.evalAt An.param
            = -(w.evalAt An.param - P.evalAt An.param) by ring, μ.map_neg]
      rw [h3]
      exact lt_of_lt_of_le hQlt (hεle w (by rw [hS]; exact hw))
    rw [h2]
  obtain ⟨-, -, ⟨-, -⟩, hzP0, -, -, -⟩ := An.mem_dom P hP
  have hfP0 : P.evalAt f ≠ 0 := by
    have hrat := (An.mem_dom P hP).1
    exact evalAt_ne_zero_of_ord_eq_zero' P hrat hf hfP
  have hfQ0 : Q.evalAt f ≠ 0 := by
    have hrat := (An.mem_dom Q hQ).1
    exact evalAt_ne_zero_of_ord_eq_zero' Q hrat hf hordQ
  rw [hQlev] at hPJQ
  have hlog : Real.log (μ (Q.evalAt f)) = Real.log (μ (P.evalAt f)) := by
    nlinarith [hPJP, hPJQ, hterms]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (μ.pos hfQ0)) (Set.mem_Ioi.mpr (μ.pos hfP0)) hlog

private theorem exists_same_level_abv_sub_lt' {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] (An : Annulus A F) (μ : AbsoluteValue L ℝ)
    (hμ : IsNonarchimedean (⇑μ)) (hA : ∀ y : L, y ∈ A ↔ μ y ≤ 1)
    {P : Place L F} (hP : P ∈ An.dom) {t : L} (ht0 : t ≠ 0) (ht : μ t < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q ∈ An.dom, Q.evalAt An.param ≠ P.evalAt An.param ∧
      μ (Q.evalAt An.param) = μ (P.evalAt An.param) ∧
      μ (Q.evalAt An.param - P.evalAt An.param) < ε := by
  obtain ⟨hrat, hzmem, ⟨hzA, hzmax⟩, hz0, m, hmmax, hmod⟩ := An.mem_dom P hP
  have hzpos : 0 < μ (P.evalAt An.param) := μ.pos hz0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hzpos) ht
  set N' := n + 1 with hN'
  have htN : μ (t ^ N') < 1 := by
    rw [map_pow]
    calc μ t ^ N' ≤ μ t ^ 1 :=
      pow_le_pow_of_le_one (μ.nonneg t) ht.le (by omega)
    _ = μ t := pow_one _
    _ < 1 := ht
  have htNlt : μ (P.evalAt An.param) * μ (t ^ N') < ε := by
    rw [map_pow, hN', pow_succ]
    have h1 : μ t ^ n * μ t ≤ μ t ^ n := by
      nlinarith [pow_nonneg (μ.nonneg t) n, μ.nonneg t]
    have h2 : μ (P.evalAt An.param) * (μ t ^ n) < ε := by
      rw [← lt_div_iff₀' hzpos]
      exact hn
    nlinarith [hzpos]
  set c : L := P.evalAt An.param * (1 + t ^ N') with hc
  have hone : μ (1 + t ^ N') = 1 := by
    rw [show (1 : L) + t ^ N' = t ^ N' + 1 by ring]
    have := abv_add_eq_of_lt μ hμ (x := t ^ N') (y := 1) (by rw [map_one]; exact htN)
    rw [map_one] at this
    exact this
  have hone0 : (1 : L) + t ^ N' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hone
    exact zero_ne_one hone
  have hcμ : μ c = μ (P.evalAt An.param) := by
    rw [hc, map_mul, hone, mul_one]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcμ
    exact hz0 (by rwa [eq_comm, map_eq_zero] at hcμ)
  have hcA : c ∈ A := (hA c).mpr (by rw [hcμ]; exact (hA _).mp hzA)
  have hcmax : (⟨c, hcA⟩ : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal_iff_abv_lt_one' μ hA]
    rw [hcμ]
    exact (mem_maximalIdeal_iff_abv_lt_one' μ hA hzA).mp hzmax

  have hmA : ((m : L) * (1 + t ^ N')⁻¹) ∈ A := by
    refine (hA _).mpr ?_
    rw [map_mul, map_inv₀, hone, inv_one, mul_one]
    exact (hA _).mp m.2
  have hmmax' : (⟨(m : L) * (1 + t ^ N')⁻¹, hmA⟩ : A) ∈ maximalIdeal A := by
    rw [mem_maximalIdeal_iff_abv_lt_one' μ hA, map_mul, map_inv₀, hone, inv_one, mul_one]
    exact (mem_maximalIdeal_iff_abv_lt_one' μ hA m.2).mp hmmax
  have hdvd : ∃ m' ∈ maximalIdeal A, (An.modulus : L) = c * (m' : L) := by
    refine ⟨⟨(m : L) * (1 + t ^ N')⁻¹, hmA⟩, hmmax', ?_⟩
    rw [hmod, hc]
    field_simp
  obtain ⟨Q, ⟨hQdom, hQz⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c, hcA⟩ hcmax hc0 hdvd
  have hQz' : Q.evalAt An.param = c := hQz
  refine ⟨Q, hQdom, ?_, ?_, ?_⟩
  · rw [hQz']
    intro h
    have h2 : P.evalAt An.param * (t ^ N') = 0 := by
      have h3 : P.evalAt An.param * (1 + t ^ N') = P.evalAt An.param := by rw [← hc, h]
      linear_combination h3
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact hz0 h4
    · exact absurd h4 (pow_ne_zero _ ht0)
  · rw [hQz', hcμ]
  · rw [hQz']
    have h1 : c - P.evalAt An.param = P.evalAt An.param * t ^ N' := by
      rw [hc]; ring
    rw [h1, map_mul]
    exact htNlt

private theorem ord_param_sub_eq_zero_of_ne' {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] (An : Annulus A F)
    {P : Place L F} (hP : P ∈ An.dom) {w : Place L F} (hw : w ∈ An.dom) (hwP : w ≠ P) :
    w.ord (An.param - algebraMap L F (P.evalAt An.param)) = 0 := by
  obtain ⟨hwrat, hwz, -, -, -⟩ := An.mem_dom w hw
  obtain ⟨-, -, -, hzP0, -⟩ := An.mem_dom P hP
  have hinj : w.evalAt An.param ≠ P.evalAt An.param := by
    intro heq
    obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, m, hmmax, hmod⟩ := An.mem_dom w hw
    obtain ⟨u, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨w.evalAt An.param, hzA⟩ hzmax hz0
      ⟨m, hmmax, hmod⟩
    exact hwP ((huniq w ⟨hw, rfl⟩).trans (huniq P ⟨hP, heq.symm⟩).symm)
  have hT0 : An.param - algebraMap L F (P.evalAt An.param) ≠ 0 := by
    intro h0
    have h1 := (An.ord_param_sub P hP)
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hmem : An.param - algebraMap L F (P.evalAt An.param) ∈ w.toValuationSubring :=
    sub_mem hwz (w.algebraMap_mem' _)
  have hval : w.evalAt (An.param - algebraMap L F (P.evalAt An.param))
      = w.evalAt An.param - P.evalAt An.param := by
    rw [GaussReduction.evalAt_sub_of_mem w hwrat hwz (w.algebraMap_mem' _),
      GaussReduction.evalAt_algebraMap_const w hwrat]
  have hnn : 0 ≤ w.ord (An.param - algebraMap L F (P.evalAt An.param)) :=
    GaussReduction.ord_nonneg_of_mem_gen w hmem hT0
  rcases hnn.eq_or_lt with heq | hlt
  · exact heq.symm
  · exfalso
    have := StandardAnnulus.evalAt_eq_zero_of_ord_pos w hT0 hlt
    rw [hval, sub_eq_zero] at this
    exact hinj this

private theorem kernel_same_level_eq' (pf : CoveringProfile)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {F : Type} [Field F]
    [Algebra (AlgebraicClosure ℚ) F] {P₀ : Place (AlgebraicClosure ℚ) F}
    {p : AlgebraicClosure ℚ} {r : ℕ} {s : Fin r → F}
    {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}
    (Γ : AdaptedCovering pf A F P₀ p s μ)
    {P W : Place (AlgebraicClosure ℚ) F} {e : Fin pf.m}
    (hPe : P ∈ (Γ.an e).dom) (hWe : W ∈ (Γ.an e).dom)
    (hlev : μ (W.evalAt (Γ.an e).param) = μ (P.evalAt (Γ.an e).param)) :
    kernel Γ W P = kernel Γ P P
      - Real.log (μ (W.evalAt (Γ.an e).param - P.evalAt (Γ.an e).param)) := by
  have hrW := Γ.retract_of_mem_an hWe
  have hrP := Γ.retract_of_mem_an hPe
  rw [kernel_eq, kernel_eq, hrW, hrP, hlev, localTerm_of_mem_an Γ hWe, localTerm_of_mem_an Γ hPe,
    if_pos hPe, if_pos hPe, sub_self, map_zero, Real.log_zero, neg_zero, hlev]
  ring

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

private theorem sum_erase_mul_kernel_an' (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (pf : CoveringProfile) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hAp : A.LiesOverPrime p) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (hμ : IsNonarchimedean (⇑μ)) (hball : ∀ y, y ∈ A ↔ μ y ≤ 1)
    (hμp : μ ((p : ℕ) : AlgebraicClosure ℚ) < 1)
    (Γ : AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
      ((p : ℕ) : AlgebraicClosure ℚ) s μ)
    {P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} {e : Fin pf.m}
    (hPe : P ∈ (Γ.an e).dom)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ w, D w = w.ord ((Γ.an e).param
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (P.evalAt (Γ.an e).param))) :
    ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
      = cfun Γ ((Γ.an e).param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (P.evalAt (Γ.an e).param)) - kernel Γ P P := by
  classical
  set T := (Γ.an e).param - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
    (P.evalAt (Γ.an e).param) with hTdef
  have hordT : P.ord T = 1 := (Γ.an e).ord_param_sub P hPe
  have hT0 : T ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hordT
    exact zero_ne_one hordT
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  obtain ⟨W, hWe, hWne, hWlev, -⟩ := exists_same_level_abv_sub_lt' (Γ.an e) μ Γ.hna Γ.ball
    hPe hp0 hμp (ε := 1) one_pos
  have hWP : W ≠ P := by
    intro h
    rw [h] at hWne
    exact hWne rfl
  have hDW : D W = 0 := by
    rw [hD]
    exact ord_param_sub_eq_zero_of_ne' (Γ.an e) hPe hWe hWP
  have hDP : D P = 1 := by rw [hD]; exact hordT

  have hkg := kernel_green N s hs p hp pf A hAp μ hμ hball hμp Γ T hT0 D hD W hDW
  have hterm : ∀ w ∈ D.support, w ≠ P → kernel Γ P w = kernel Γ W w := by
    intro w hw hwP
    have hword : w.ord T ≠ 0 := by
      rw [← hD]
      exact Finsupp.mem_support_iff.mp hw
    have hwdom : w ∉ (Γ.an e).dom := by
      intro hwdom
      exact hword (ord_param_sub_eq_zero_of_ne' (Γ.an e) hPe hwdom hwP)
    have hrPW : Γ.retract W = Γ.retract P := by
      rw [Γ.retract_of_mem_an hPe, Γ.retract_of_mem_an hWe, hWlev]
    rw [kernel_eq, kernel_eq, hrPW, localTerm_of_mem_an Γ hPe, localTerm_of_mem_an Γ hWe,
      if_neg hwdom, if_neg hwdom]

  have htrans : ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
      = ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ W w) := by
    refine Finsupp.sum_congr fun w hw => ?_
    rw [Finsupp.support_erase, Finset.mem_erase] at hw
    rw [hterm w hw.2 hw.1]

  have hsplit : (D.sum fun w n => (n : ℝ) * kernel Γ W w)
      = ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ W w) + (D P : ℝ) * kernel Γ W P := by
    conv_lhs => rw [← Finsupp.erase_add_single P D]
    rw [Finsupp.sum_add_index' (fun w => by simp) (fun w b₁ b₂ => by push_cast; ring),
      Finsupp.sum_single_index (by simp)]
  have hWval : W.evalAt T = W.evalAt (Γ.an e).param - P.evalAt (Γ.an e).param := by
    obtain ⟨hWrat, hWz, -, -, -⟩ := (Γ.an e).mem_dom W hWe
    rw [hTdef, GaussReduction.evalAt_sub_of_mem W hWrat hWz (W.algebraMap_mem' _),
      GaussReduction.evalAt_algebraMap_const W hWrat]
  have hker : kernel Γ W P = kernel Γ P P - Real.log (μ (W.evalAt T)) := by
    rw [hWval]
    exact kernel_same_level_eq' pf Γ hPe hWe hWlev
  rw [htrans]
  rw [hsplit, hDP] at hkg
  rw [hker] at hkg
  push_cast at hkg
  linarith

private noncomputable def gfun {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (P : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) : Fin r → F :=
  fun j => s j * (s (pivotIndex s P hr))⁻¹

private noncomputable def mfun {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (P : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) : Fin r × Fin r → F :=
  fun q => (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1) * (s (pivotIndex s P hr))⁻¹

private noncomputable def dgn {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (P : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) : Fin r → ℕ :=
  fun j => (P.ord (gfun s P hr j)).toNat

private noncomputable def dmn {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (P : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) : Fin r × Fin r → ℕ :=
  fun q => (P.ord (mfun s P hr q)).toNat

private noncomputable def gsh {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (P : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (T : F) : Fin r → F :=
  fun j => gfun s P hr j * (T ^ dgn s P hr j)⁻¹

private noncomputable def msh {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (P : Place (AlgebraicClosure ℚ) F) (hr : 0 < r) (T : F) :
    Fin r × Fin r → F :=
  fun q => mfun s P hr q * (T ^ dmn s P hr q)⁻¹

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

private theorem prox_eval_eq' (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ j, s j ≠ 0)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hr : 0 < r)
    (P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hPrat : P.IsRational) (hQrat : Q.IsRational)
    (T : modularFunctionFieldBar N) (haQ : Q.evalAt T ≠ 0)
    (hgmem : ∀ j, gfun s P hr j ∈ Q.toValuationSubring)
    (hSpos : 0 < ⨆ q : Fin r × Fin r,
      μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
    (hγval : ∀ j, μ (Q.evalAt (gfun s P hr j)) = μ (evalVec s P j)
       ∨ (μ (Q.evalAt (gfun s P hr j)) < 1 ∧ μ (evalVec s P j) = 0))
    (hβval : ∀ q : Fin r × Fin r, μ (Q.evalAt (mfun s P hr q))
         = μ (Q.evalAt T) * μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1))
       ∨ (μ (Q.evalAt (mfun s P hr q)) < μ (Q.evalAt T) * (⨆ q' : Fin r × Fin r,
            μ (regVal s P T 1 1 (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)))
          ∧ μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) = 0)) :
    prox (⇑μ) (evalVec s P) (evalVec s Q)
      = 2 * Real.log (⨆ i, μ (evalVec s P i)) - Real.log (μ (Q.evalAt T))
        - Real.log (⨆ q : Fin r × Fin r,
            μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1))) := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  set x : Fin r → AlgebraicClosure ℚ := evalVec s P with hx
  set x' : Fin r → AlgebraicClosure ℚ := fun j => Q.evalAt (gfun s P hr j) with hx'
  set Sreg : ℝ := ⨆ q : Fin r × Fin r,
    μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) with hSreg

  have hxpivot : x (pivotIndex s P hr) = 1 := evalVec_pivot' s P hr hPrat hs0
  have hsupx1 : 1 ≤ ⨆ j, μ (x j) := by
    have h1 : μ (x (pivotIndex s P hr)) = 1 := by rw [hxpivot, map_one]
    rw [← h1]
    exact le_ciSup (f := fun j => μ (x j)) (Set.Finite.bddAbove (Set.finite_range _)) _
  have hsupxpos : 0 < ⨆ j, μ (x j) := lt_of_lt_of_le one_pos hsupx1

  set c' : AlgebraicClosure ℚ
    := Q.evalAt (s (pivotIndex s P hr) * (s (pivotIndex s Q hr))⁻¹) with hc'
  have hbridge : ∀ j, evalVec s Q j = x' j * c' := by
    intro j
    rw [evalVec_eq' s Q hr j, hx', hc']
    have harg : s j * (s (pivotIndex s Q hr))⁻¹
        = gfun s P hr j * (s (pivotIndex s P hr) * (s (pivotIndex s Q hr))⁻¹) := by
      unfold gfun
      have h9 : s j * (s (pivotIndex s P hr))⁻¹
            * (s (pivotIndex s P hr) * (s (pivotIndex s Q hr))⁻¹)
          = s j * ((s (pivotIndex s P hr))⁻¹ * s (pivotIndex s P hr))
            * (s (pivotIndex s Q hr))⁻¹ := by
        ring
      rw [h9, inv_mul_cancel₀ (hs0 _), mul_one]
    rw [harg]
    exact GaussReduction.evalAt_mul_of_mem Q hQrat (hgmem j) (pivot_ratio_mem' s Q hr hs0 _)
  have hc'0 : c' ≠ 0 := by
    intro h0
    have h1 : evalVec s Q (pivotIndex s Q hr) = 1 := evalVec_pivot' s Q hr hQrat hs0
    rw [hbridge (pivotIndex s Q hr), h0, mul_zero] at h1
    exact zero_ne_one h1

  have hsupx' : (⨆ j, μ (x' j)) = ⨆ j, μ (x j) := by
    refine le_antisymm ?_ ?_
    · refine Real.iSup_le (fun j => ?_) (le_trans zero_le_one hsupx1)
      rcases hγval j with h | ⟨h1, -⟩
      · rw [hx', h]
        exact le_ciSup (f := fun j => μ (x j)) (Set.Finite.bddAbove (Set.finite_range _)) j
      · exact le_trans h1.le hsupx1
    · refine Real.iSup_le (fun j => ?_) (Real.iSup_nonneg fun j => μ.nonneg _)
      rcases hγval j with h | ⟨-, h0⟩
      · rw [hx, ← h]
        exact le_ciSup (f := fun j => μ (x' j)) (Set.Finite.bddAbove (Set.finite_range _)) j
      · rw [hx, h0]
        exact Real.iSup_nonneg fun j => μ.nonneg _

  have hminor_eq : ∀ q : Fin r × Fin r,
      x q.1 * x' q.2 - x q.2 * x' q.1 = Q.evalAt (mfun s P hr q) := by
    intro q
    have hlin := evalAt_smul_sub_smul Q hQrat (x q.1) (x q.2) (hgmem q.2) (hgmem q.1)
    have harg : x q.1 • gfun s P hr q.2 - x q.2 • gfun s P hr q.1 = mfun s P hr q := by
      unfold gfun mfun
      simp only [Algebra.smul_def, hx]
      ring
    rw [hx', ← hlin, harg]

  have hminorsup : (⨆ q : Fin r × Fin r, μ (x q.1 * x' q.2 - x q.2 * x' q.1))
      = μ (Q.evalAt T) * Sreg := by
    have haQpos : 0 < μ (Q.evalAt T) := μ.pos haQ
    refine le_antisymm ?_ ?_
    · refine Real.iSup_le (fun q => ?_) (mul_nonneg (μ.nonneg _) (le_of_lt hSpos))
      rw [hminor_eq q]
      rcases hβval q with h | ⟨h1, -⟩
      · rw [h]
        refine mul_le_mul_of_nonneg_left ?_ (μ.nonneg _)
        exact le_ciSup (f := fun q' : Fin r × Fin r => μ (regVal s P T 1 1
          (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)))
          (Set.Finite.bddAbove (Set.finite_range _)) q
      · exact le_of_lt h1
    · obtain ⟨qh, hqh⟩ := Finite.exists_max (fun q : Fin r × Fin r =>
        μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      have hSeq : Sreg = μ (regVal s P T 1 1
          (evalVec s P qh.1 • s qh.2 - evalVec s P qh.2 • s qh.1)) := by
        refine le_antisymm (Real.iSup_le (fun q => hqh q) (μ.nonneg _)) ?_
        exact le_ciSup (f := fun q' : Fin r × Fin r => μ (regVal s P T 1 1
          (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)))
          (Set.Finite.bddAbove (Set.finite_range _)) qh
      rcases hβval qh with h | ⟨-, h0⟩
      · have h2 : μ (Q.evalAt T) * Sreg = μ (x qh.1 * x' qh.2 - x qh.2 * x' qh.1) := by
          rw [hminor_eq qh, h, hSeq]
        rw [h2]
        exact le_ciSup (f := fun q : Fin r × Fin r => μ (x q.1 * x' q.2 - x q.2 * x' q.1))
          (Set.Finite.bddAbove (Set.finite_range _)) qh
      · rw [hSeq, h0] at hSpos
        exact absurd hSpos (lt_irrefl 0)

  have hsupx'pos : 0 < ⨆ j, μ (x' j) := by rw [hsupx']; exact hsupxpos
  have hminorpos : 0 < ⨆ q : Fin r × Fin r, μ (x q.1 * x' q.2 - x q.2 * x' q.1) := by
    rw [hminorsup]
    exact mul_pos (μ.pos haQ) hSpos

  have hfun : evalVec s Q = fun j => c' * x' j := funext fun j => by rw [hbridge j]; ring
  rw [hfun, prox_smul_right' μ x x' hc'0 hsupx'pos hminorpos]
  unfold prox
  rw [hminorsup, Real.log_mul (ne_of_gt (μ.pos haQ)) (ne_of_gt hSpos), hsupx']
  ring

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in

private theorem abs_bracket_le_of_Q (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (pf : CoveringProfile) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hAp : A.LiesOverPrime p) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (hμ : IsNonarchimedean (⇑μ)) (hball : ∀ y, y ∈ A ↔ μ y ≤ 1)
    (hμp : μ ((p : ℕ) : AlgebraicClosure ℚ) < 1)
    (Γ : AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
      ((p : ℕ) : AlgebraicClosure ℚ) s μ)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (u : modularFunctionFieldBar N) (hu : P.ord u = 1)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ w, D w = w.ord u)
    (T : modularFunctionFieldBar N) (hT0 : T ≠ 0) (hordT : P.ord T = 1)
    (diag : ℝ)
    (hdiagid : ∀ D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, D' w = w.ord T) →
      ((D'.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) = cfun Γ T - diag)
    (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (_hQP : Q ≠ P)
    (hker : kernel Γ P Q = diag - Real.log (μ (Q.evalAt T)))
    (hprox : prox (⇑μ) (evalVec s P) (evalVec s Q)
       = 2 * Real.log (⨆ i, μ (evalVec s P i)) - Real.log (μ (Q.evalAt T))
         - Real.log (⨆ q : Fin r × Fin r,
             μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1))))
    (C : ℝ)
    (hC : |kernel Γ P Q - prox (⇑μ) (evalVec s P) (evalVec s Q)|
      ≤ C * (-Real.log (μ ((p : ℕ) : AlgebraicClosure ℚ)))) :
    |((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) - cfun Γ u
        - (Real.log (⨆ q : Fin r × Fin r,
              μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
           - 2 * Real.log (⨆ i, μ (evalVec s P i)))|
      ≤ C * (-Real.log (μ ((p : ℕ) : AlgebraicClosure ℚ))) := by
  classical
  have hratall : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational :=
    fun w => OfTopTransport.isRational_of_deg_eq_one w (deg_eq_one_modularFunctionFieldBar N w)
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N

  obtain ⟨q₀, hq₀⟩ := exists_regVal_chord_ne_zero N s hs P hu
  have hr : 0 < r := q₀.1.pos
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hs0 : ∀ j, s j ≠ 0 := fun j => hs.1.ne_zero j

  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hu
    exact zero_ne_one hu
  set v : modularFunctionFieldBar N := u * T⁻¹ with hv
  have hv0 : v ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hT0)
  have huTv : u = T * v := by
    rw [hv]
    field_simp
  have hordv : P.ord v = 0 := by
    rw [hv, P.ord_mul hu0 (inv_ne_zero hT0), P.ord_inv, hu, hordT]
    ring
  have hvmem : v ∈ P.toValuationSubring :=
    GaussReduction.mem_of_ord_nonneg_gen P hv0 hordv.ge
  have hvinvmem : v⁻¹ ∈ P.toValuationSubring := by
    refine GaussReduction.mem_of_ord_nonneg_gen P (inv_ne_zero hv0) ?_
    rw [P.ord_inv, hordv, neg_zero]
  have hvP0 : P.evalAt v ≠ 0 :=
    evalAt_ne_zero_of_ord_eq_zero' P (hratall P) hv0 hordv
  have hvinv_val : P.evalAt v⁻¹ = (P.evalAt v)⁻¹ := by
    have h1 : P.evalAt v * P.evalAt v⁻¹ = 1 := by
      rw [← GaussReduction.evalAt_mul_of_mem P (hratall P) hvmem hvinvmem,
        mul_inv_cancel₀ hv0, P.evalAt_one]
    exact eq_inv_of_mul_eq_one_right h1

  obtain ⟨DT, hDT, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) T hT0
  obtain ⟨Dv, hDv, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) v hv0
  have hsplitD : D = DT + Dv := by
    ext w
    rw [Finsupp.add_apply, hD w, hDT w, hDv w, huTv, w.ord_mul hT0 hv0]
  have hDvP : Dv P = 0 := by rw [hDv]; exact hordv
  have herasev : Dv.erase P = Dv := by
    ext w
    rw [Finsupp.erase_apply]
    split_ifs with h
    · rw [h, hDvP]
    · rfl
  have hsum_split : ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
      = ((DT.erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
        + (Dv.sum fun w n => (n : ℝ) * kernel Γ P w) := by
    rw [hsplitD, Finsupp.erase_add,
      Finsupp.sum_add_index' (fun w => by simp) (fun w b₁ b₂ => by push_cast; ring), herasev]
  have hgreenv := kernel_green N s hs p hp pf A hAp μ hμ hball hμp Γ v hv0 Dv hDv P hDvP
  have hTdiag := hdiagid DT hDT
  have hcfun : cfun Γ u = cfun Γ T + cfun Γ v := by
    rw [huTv]
    exact cfun_mul Γ hT0 hv0

  have hreg_eq : ∀ q : Fin r × Fin r,
      regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
        = regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (P.evalAt v)⁻¹ := by
    intro q
    unfold regVal
    rw [dif_pos hr, dif_pos hr]
    simp only [pow_one]
    by_cases hσ : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1) = 0
    · rw [hσ]
      simp only [zero_mul, evalAt_zero_aux P (hratall P)]
    · have hmmem : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (s (pivotIndex s P hr))⁻¹ ∈ P.toValuationSubring := by
        have h1 : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
            * (s (pivotIndex s P hr))⁻¹
            = evalVec s P q.1 • (s q.2 * (s (pivotIndex s P hr))⁻¹)
              - evalVec s P q.2 • (s q.1 * (s (pivotIndex s P hr))⁻¹) := by
          simp only [Algebra.smul_def]
          ring
        rw [h1]
        refine sub_mem ?_ ?_
        · rw [Algebra.smul_def]
          exact mul_mem (P.algebraMap_mem' _) (pivot_ratio_mem' s P hr hs0 q.2)
        · rw [Algebra.smul_def]
          exact mul_mem (P.algebraMap_mem' _) (pivot_ratio_mem' s P hr hs0 q.1)
      have hmval : P.evalAt ((evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (s (pivotIndex s P hr))⁻¹) = 0 := by
        have h1 : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
            * (s (pivotIndex s P hr))⁻¹
            = evalVec s P q.1 • (s q.2 * (s (pivotIndex s P hr))⁻¹)
              - evalVec s P q.2 • (s q.1 * (s (pivotIndex s P hr))⁻¹) := by
          simp only [Algebra.smul_def]
          ring
        rw [h1, evalAt_smul_sub_smul P (hratall P) _ _
          (pivot_ratio_mem' s P hr hs0 q.2) (pivot_ratio_mem' s P hr hs0 q.1),
          ← evalVec_eq' s P hr, ← evalVec_eq' s P hr]
        ring
      have hm0 : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (s (pivotIndex s P hr))⁻¹ ≠ 0 :=
        mul_ne_zero hσ (inv_ne_zero (hs0 _))
      have hmord : 1 ≤ P.ord ((evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (s (pivotIndex s P hr))⁻¹) :=
        one_le_ord_of_evalAt_eq_zero' P (hratall P) hm0 hmmem hmval
      have hf1mem : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (s (pivotIndex s P hr))⁻¹ * T⁻¹ ∈ P.toValuationSubring := by
        refine GaussReduction.mem_of_ord_nonneg_gen P
          (mul_ne_zero hm0 (inv_ne_zero hT0)) ?_
        rw [P.ord_mul hm0 (inv_ne_zero hT0), P.ord_inv, hordT]
        omega
      have huinv : u⁻¹ = T⁻¹ * v⁻¹ := by
        rw [huTv, mul_inv]
      rw [huinv, show (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
          * (s (pivotIndex s P hr))⁻¹ * (T⁻¹ * v⁻¹)
          = ((evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
            * (s (pivotIndex s P hr))⁻¹ * T⁻¹) * v⁻¹ by ring,
        GaussReduction.evalAt_mul_of_mem P (hratall P) hf1mem hvinvmem, hvinv_val]

  have hsupscale : (⨆ q : Fin r × Fin r,
        μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      = (⨆ q : Fin r × Fin r,
          μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
        * (μ (P.evalAt v))⁻¹ := by
    rw [← ciSup_mul_const_aux' (fun q : Fin r × Fin r =>
        μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      ((μ (P.evalAt v))⁻¹) (fun q => μ.nonneg _) (inv_nonneg.mpr (μ.nonneg _))]
    refine iSup_congr fun q => ?_
    rw [hreg_eq q, map_mul, map_inv₀]

  obtain ⟨q₁, hq₁⟩ := exists_regVal_chord_ne_zero N s hs P hordT
  have hsupT : 0 < ⨆ q : Fin r × Fin r,
      μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) :=
    lt_of_lt_of_le (μ.pos hq₁) (le_ciSup (f := fun q : Fin r × Fin r => μ (regVal s P T 1 1
      (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      (Set.Finite.bddAbove (Set.finite_range _)) q₁)
  have hsupu : 0 < ⨆ q : Fin r × Fin r,
      μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) :=
    lt_of_lt_of_le (μ.pos hq₀) (le_ciSup (f := fun q : Fin r × Fin r => μ (regVal s P u 1 1
      (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      (Set.Finite.bddAbove (Set.finite_range _)) q₀)
  have hμvpos : 0 < μ (P.evalAt v) := μ.pos hvP0
  have hlogscale : Real.log (⨆ q : Fin r × Fin r,
        μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      = Real.log (⨆ q : Fin r × Fin r,
          μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
        - Real.log (μ (P.evalAt v)) := by
    rw [hsupscale, Real.log_mul (ne_of_gt hsupT) (inv_ne_zero (ne_of_gt hμvpos)),
      Real.log_inv]
    ring

  have hX : ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) - cfun Γ u
      - (Real.log (⨆ q : Fin r × Fin r,
            μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
         - 2 * Real.log (⨆ i, μ (evalVec s P i)))
      = -(kernel Γ P Q - prox (⇑μ) (evalVec s P) (evalVec s Q)) := by
    rw [hker, hprox]
    have h1 := hsum_split
    have h2 := hgreenv
    have h3 := hTdiag
    have h4 := hcfun
    have h5 := hlogscale
    linarith
  rw [hX, abs_neg]
  exact hC

private theorem ord_one' {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (v : Place L F) : v.ord (1 : F) = 0 := by
  have h := v.ord_mul (one_ne_zero (α := F)) (one_ne_zero (α := F))
  rw [mul_one] at h
  omega

private theorem ord_pow' {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (v : Place L F) {f : F} (hf : f ≠ 0) : ∀ d : ℕ, v.ord (f ^ d) = d * v.ord f := by
  intro d
  induction d with
  | zero => rw [pow_zero, ord_one']; ring
  | succ d ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero d hf) hf, ih]
    push_cast
    ring

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in

private theorem exists_Q_prox' (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r)
    (T : modularFunctionFieldBar N) (hT0 : T ≠ 0) (hordT : P.ord T = 1)
    (QC : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Prop)
    (hstab : ∀ f : modularFunctionFieldBar N, f ≠ 0 → P.ord f = 0 →
      ∃ ε > 0, ∀ Q, QC Q → Q.evalAt T ≠ 0 → μ (Q.evalAt T) < ε →
        μ (Q.evalAt f) = μ (P.evalAt f) ∧ Q.ord f = 0)
    (hprod : ∀ δ > 0, ∃ Q, QC Q ∧ Q.evalAt T ≠ 0 ∧ μ (Q.evalAt T) < δ)
    (hordQT : ∀ Q, QC Q → Q.evalAt T ≠ 0 → Q.ord T = 0) :
    ∃ Q, QC Q ∧ Q ≠ P ∧ Q.evalAt T ≠ 0 ∧
      prox (⇑μ) (evalVec s P) (evalVec s Q)
        = 2 * Real.log (⨆ i, μ (evalVec s P i)) - Real.log (μ (Q.evalAt T))
          - Real.log (⨆ q : Fin r × Fin r,
              μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1))) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hratall : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational :=
    fun w => OfTopTransport.isRational_of_deg_eq_one w (deg_eq_one_modularFunctionFieldBar N w)
  have hs0 : ∀ j, s j ≠ 0 := fun j => hs.1.ne_zero j
  have hPT0 : P.evalAt T = 0 :=
    StandardAnnulus.evalAt_eq_zero_of_ord_pos P hT0 (by rw [hordT]; exact one_pos)

  have hg0 : ∀ j, gfun s P hr j ≠ 0 := fun j =>
    mul_ne_zero (hs0 j) (inv_ne_zero (hs0 _))
  have hgord : ∀ j, 0 ≤ P.ord (gfun s P hr j) := by
    intro j
    unfold gfun
    rw [P.ord_mul (hs0 j) (inv_ne_zero (hs0 _)), P.ord_inv]
    have := pivot_spec' s P hr j
    omega
  have hgord_eq : ∀ j, P.ord (gfun s P hr j) = (dgn s P hr j : ℤ) := by
    intro j
    unfold dgn
    rw [Int.toNat_of_nonneg (hgord j)]
  have hgsh0 : ∀ j, gsh s P hr T j ≠ 0 := fun j =>
    mul_ne_zero (hg0 j) (inv_ne_zero (pow_ne_zero _ hT0))
  have hgshord : ∀ j, P.ord (gsh s P hr T j) = 0 := by
    intro j
    unfold gsh
    rw [P.ord_mul (hg0 j) (inv_ne_zero (pow_ne_zero _ hT0)), P.ord_inv, ord_pow' P hT0,
      hordT, hgord_eq j]
    ring

  have hmmem : ∀ q : Fin r × Fin r, mfun s P hr q ∈ P.toValuationSubring := by
    intro q
    unfold mfun
    have h1 : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
        * (s (pivotIndex s P hr))⁻¹
        = evalVec s P q.1 • (s q.2 * (s (pivotIndex s P hr))⁻¹)
          - evalVec s P q.2 • (s q.1 * (s (pivotIndex s P hr))⁻¹) := by
      simp only [Algebra.smul_def]
      ring
    rw [h1]
    refine sub_mem ?_ ?_
    · rw [Algebra.smul_def]
      exact mul_mem (P.algebraMap_mem' _) (pivot_ratio_mem' s P hr hs0 q.2)
    · rw [Algebra.smul_def]
      exact mul_mem (P.algebraMap_mem' _) (pivot_ratio_mem' s P hr hs0 q.1)
  have hmval : ∀ q : Fin r × Fin r, P.evalAt (mfun s P hr q) = 0 := by
    intro q
    unfold mfun
    have h1 : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
        * (s (pivotIndex s P hr))⁻¹
        = evalVec s P q.1 • (s q.2 * (s (pivotIndex s P hr))⁻¹)
          - evalVec s P q.2 • (s q.1 * (s (pivotIndex s P hr))⁻¹) := by
      simp only [Algebra.smul_def]
      ring
    rw [h1, evalAt_smul_sub_smul P (hratall P) _ _
      (pivot_ratio_mem' s P hr hs0 q.2) (pivot_ratio_mem' s P hr hs0 q.1),
      ← evalVec_eq' s P hr, ← evalVec_eq' s P hr]
    ring
  have hmord1 : ∀ q : Fin r × Fin r, mfun s P hr q ≠ 0 → 1 ≤ P.ord (mfun s P hr q) :=
    fun q hmq =>
      one_le_ord_of_evalAt_eq_zero' P (hratall P) hmq (hmmem q) (hmval q)
  have hmord_eq : ∀ q, mfun s P hr q ≠ 0 → P.ord (mfun s P hr q) = (dmn s P hr q : ℤ) := by
    intro q hmq
    unfold dmn
    rw [Int.toNat_of_nonneg (le_trans zero_le_one (hmord1 q hmq))]
  have hmshord : ∀ q, mfun s P hr q ≠ 0 → P.ord (msh s P hr T q) = 0 := by
    intro q hmq
    unfold msh
    rw [P.ord_mul hmq (inv_ne_zero (pow_ne_zero _ hT0)), P.ord_inv, ord_pow' P hT0,
      hordT, hmord_eq q hmq]
    ring

  have hch_g : ∀ j, ∃ ε > 0, ∀ Q, QC Q → Q.evalAt T ≠ 0 → μ (Q.evalAt T) < ε →
      μ (Q.evalAt (gsh s P hr T j)) = μ (P.evalAt (gsh s P hr T j))
        ∧ Q.ord (gsh s P hr T j) = 0 :=
    fun j => hstab (gsh s P hr T j) (hgsh0 j) (hgshord j)
  choose εg hεg hlawg using hch_g
  have hch_m : ∀ q : Fin r × Fin r, ∃ ε > 0, mfun s P hr q ≠ 0 →
      ∀ Q, QC Q → Q.evalAt T ≠ 0 → μ (Q.evalAt T) < ε →
      μ (Q.evalAt (msh s P hr T q)) = μ (P.evalAt (msh s P hr T q))
        ∧ Q.ord (msh s P hr T q) = 0 := by
    intro q
    by_cases hmq : mfun s P hr q = 0
    · exact ⟨1, one_pos, fun h => absurd hmq h⟩
    · obtain ⟨ε, hε, hlaw⟩ := hstab (msh s P hr T q)
        (mul_ne_zero hmq (inv_ne_zero (pow_ne_zero _ hT0))) (hmshord q hmq)
      exact ⟨ε, hε, fun _ => hlaw⟩
  choose εm hεm hlawm using hch_m

  have hSpos : 0 < ⨆ q : Fin r × Fin r,
      μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) := by
    obtain ⟨q₁, hq₁⟩ := exists_regVal_chord_ne_zero N s hs P hordT
    exact lt_of_lt_of_le (μ.pos hq₁) (le_ciSup (f := fun q : Fin r × Fin r => μ (regVal s P T 1 1
      (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
      (Set.Finite.bddAbove (Set.finite_range _)) q₁)
  obtain ⟨jg, hjg⟩ := Finite.exists_min (fun j : Fin r => εg j)
  obtain ⟨qm, hqm⟩ := Finite.exists_min (fun q : Fin r × Fin r => εm q)
  obtain ⟨jθ, hjθ⟩ := Finite.exists_min (fun j : Fin r =>
    (1 : ℝ) / (μ (P.evalAt (gsh s P hr T j)) + 1))
  obtain ⟨qθ, hqθ⟩ := Finite.exists_min (fun q : Fin r × Fin r =>
    (⨆ q' : Fin r × Fin r, μ (regVal s P T 1 1
        (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)))
      / (μ (P.evalAt (msh s P hr T q)) + 1))
  set δ0 : ℝ := min (min (εg jg) (εm qm))
    (min ((1 : ℝ) / (μ (P.evalAt (gsh s P hr T jθ)) + 1))
      (min ((⨆ q' : Fin r × Fin r, μ (regVal s P T 1 1
          (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)))
        / (μ (P.evalAt (msh s P hr T qθ)) + 1)) 1)) with hδ0
  have hδ0pos : 0 < δ0 := by
    rw [hδ0]
    refine lt_min (lt_min (hεg jg) (hεm qm)) (lt_min ?_ (lt_min ?_ one_pos))
    · positivity
    · positivity
  obtain ⟨Q, hQC, haQ0, haQlt⟩ := hprod δ0 hδ0pos
  have hQP : Q ≠ P := by
    intro h
    rw [h, hPT0] at haQ0
    exact haQ0 rfl
  have haQpos : 0 < μ (Q.evalAt T) := μ.pos haQ0
  have haQle1 : μ (Q.evalAt T) ≤ 1 := by
    have h1 : δ0 ≤ 1 := by
      rw [hδ0]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    exact le_trans haQlt.le h1
  have hQT : Q.ord T = 0 := hordQT Q hQC haQ0
  have hQTmem : T ∈ Q.toValuationSubring :=
    GaussReduction.mem_of_ord_nonneg_gen Q hT0 hQT.ge

  have hlawg' : ∀ j, μ (Q.evalAt (gsh s P hr T j)) = μ (P.evalAt (gsh s P hr T j))
      ∧ Q.ord (gsh s P hr T j) = 0 := by
    intro j
    refine hlawg j Q hQC haQ0 (lt_of_lt_of_le haQlt ?_)
    rw [hδ0]
    exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (hjg j))
  have hlawm' : ∀ q, mfun s P hr q ≠ 0 →
      μ (Q.evalAt (msh s P hr T q)) = μ (P.evalAt (msh s P hr T q))
        ∧ Q.ord (msh s P hr T q) = 0 := by
    intro q hmq
    refine hlawm q hmq Q hQC haQ0 (lt_of_lt_of_le haQlt ?_)
    rw [hδ0]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (hqm q))

  have hgfact : ∀ j, gfun s P hr j = gsh s P hr T j * T ^ dgn s P hr j := by
    intro j
    unfold gsh
    field_simp
  have hgmemQ : ∀ j, gfun s P hr j ∈ Q.toValuationSubring := by
    intro j
    rw [hgfact j]
    exact mul_mem (GaussReduction.mem_of_ord_nonneg_gen Q (hgsh0 j) (hlawg' j).2.ge)
      (pow_mem hQTmem _)
  have hgvalQ : ∀ j, μ (Q.evalAt (gfun s P hr j))
      = μ (P.evalAt (gsh s P hr T j)) * μ (Q.evalAt T) ^ dgn s P hr j := by
    intro j
    rw [hgfact j, GaussReduction.evalAt_mul_of_mem Q (hratall Q)
        (GaussReduction.mem_of_ord_nonneg_gen Q (hgsh0 j) (hlawg' j).2.ge) (pow_mem hQTmem _),
      evalAt_pow_of_mem' Q (hratall Q) hQTmem, map_mul, map_pow, (hlawg' j).1]

  have hγval : ∀ j, μ (Q.evalAt (gfun s P hr j)) = μ (evalVec s P j)
      ∨ (μ (Q.evalAt (gfun s P hr j)) < 1 ∧ μ (evalVec s P j) = 0) := by
    intro j
    by_cases hd : dgn s P hr j = 0
    · left
      have hgsh_eq : gsh s P hr T j = gfun s P hr j := by
        unfold gsh
        rw [hd, pow_zero, inv_one, mul_one]
      calc μ (Q.evalAt (gfun s P hr j))
          = μ (P.evalAt (gsh s P hr T j)) * μ (Q.evalAt T) ^ dgn s P hr j := hgvalQ j
        _ = μ (P.evalAt (gsh s P hr T j)) := by rw [hd, pow_zero, mul_one]
        _ = μ (evalVec s P j) := by
            rw [hgsh_eq, evalVec_eq' s P hr]
            unfold gfun
            rfl
    · right
      have hd1 : 1 ≤ dgn s P hr j := by omega
      constructor
      · have hM := hgvalQ j
        set M : ℝ := μ (P.evalAt (gsh s P hr T j)) with hMdef
        set a : ℝ := μ (Q.evalAt T) with hadef
        have h1 : a ^ dgn s P hr j ≤ a := by
          calc a ^ dgn s P hr j ≤ a ^ 1 :=
            pow_le_pow_of_le_one (by rw [hadef]; exact μ.nonneg _) haQle1 hd1
          _ = a := pow_one _
        have h2 : a < (1 : ℝ) / (M + 1) := by
          refine lt_of_lt_of_le haQlt ?_
          rw [hδ0]
          exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (hjθ j))
        have h3 : 0 ≤ M := by rw [hMdef]; exact μ.nonneg _
        have h4 : 0 < M + 1 := by linarith
        rw [lt_div_iff₀ h4] at h2
        have h5 : M * a ^ dgn s P hr j ≤ M * a := mul_le_mul_of_nonneg_left h1 h3
        rw [hM]
        nlinarith [haQpos.le]
      · rw [evalVec_eq' s P hr]
        show μ (P.evalAt (gfun s P hr j)) = 0
        rw [StandardAnnulus.evalAt_eq_zero_of_ord_pos P (hg0 j)
          (by rw [hgord_eq j]; omega), map_zero]

  have hβval : ∀ q : Fin r × Fin r, μ (Q.evalAt (mfun s P hr q))
      = μ (Q.evalAt T) * μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1))
      ∨ (μ (Q.evalAt (mfun s P hr q)) < μ (Q.evalAt T) * (⨆ q' : Fin r × Fin r,
            μ (regVal s P T 1 1 (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)))
         ∧ μ (regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) = 0) := by
    intro q
    have hregT_eq : regVal s P T 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)
        = P.evalAt (mfun s P hr q * T⁻¹) := by
      unfold regVal mfun
      rw [dif_pos hr]
      simp only [pow_one]
    by_cases hmq : mfun s P hr q = 0
    · left
      have h1 : (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1) = 0 ∨
          (s (pivotIndex s P hr))⁻¹ = 0 := mul_eq_zero.mp hmq
      rcases h1 with h1 | h1
      · rw [hregT_eq, hmq, zero_mul, evalAt_zero_aux P (hratall P), map_zero, mul_zero,
          evalAt_zero_aux Q (hratall Q), map_zero]
      · exact absurd h1 (inv_ne_zero (hs0 _))
    · have hmfact : mfun s P hr q = msh s P hr T q * T ^ dmn s P hr q := by
        unfold msh
        field_simp
      have hmshmemQ : msh s P hr T q ∈ Q.toValuationSubring :=
        GaussReduction.mem_of_ord_nonneg_gen Q
          (mul_ne_zero hmq (inv_ne_zero (pow_ne_zero _ hT0))) (hlawm' q hmq).2.ge
      have hmvalQ : μ (Q.evalAt (mfun s P hr q))
          = μ (P.evalAt (msh s P hr T q)) * μ (Q.evalAt T) ^ dmn s P hr q := by
        rw [hmfact, GaussReduction.evalAt_mul_of_mem Q (hratall Q) hmshmemQ (pow_mem hQTmem _),
          evalAt_pow_of_mem' Q (hratall Q) hQTmem, map_mul, map_pow, (hlawm' q hmq).1]
      by_cases hd : dmn s P hr q = 1
      · left
        calc μ (Q.evalAt (mfun s P hr q))
            = μ (P.evalAt (msh s P hr T q)) * μ (Q.evalAt T) ^ dmn s P hr q := hmvalQ
          _ = μ (Q.evalAt T) * μ (P.evalAt (msh s P hr T q)) := by
              rw [hd, pow_one]; ring
          _ = μ (Q.evalAt T) * μ (regVal s P T 1 1
                (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) := by
              rw [hregT_eq]
              congr 2
              unfold msh
              rw [hd, pow_one]
      · right
        have hd2 : 2 ≤ dmn s P hr q := by
          have := hmord1 q hmq
          rw [hmord_eq q hmq] at this
          omega
        constructor
        · have hM := hmvalQ
          set M : ℝ := μ (P.evalAt (msh s P hr T q)) with hMdef
          set a : ℝ := μ (Q.evalAt T) with hadef
          set S : ℝ := ⨆ q' : Fin r × Fin r, μ (regVal s P T 1 1
            (evalVec s P q'.1 • s q'.2 - evalVec s P q'.2 • s q'.1)) with hSdef
          have h1 : a ^ dmn s P hr q ≤ a ^ 2 :=
            pow_le_pow_of_le_one (by rw [hadef]; exact μ.nonneg _) haQle1 hd2
          have h2 : a < S / (M + 1) := by
            refine lt_of_lt_of_le haQlt ?_
            rw [hδ0]
            exact le_trans (min_le_right _ _)
              (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (hqθ q)))
          have h3 : 0 ≤ M := by rw [hMdef]; exact μ.nonneg _
          have h4 : 0 < M + 1 := by linarith
          rw [lt_div_iff₀ h4] at h2
          have h5 : M * a ^ dmn s P hr q ≤ M * a ^ 2 := mul_le_mul_of_nonneg_left h1 h3
          rw [hM]
          nlinarith [haQpos.le, haQpos, sq_nonneg a]
        · rw [hregT_eq]
          have hord2 : 0 < P.ord (mfun s P hr q * T⁻¹) := by
            rw [P.ord_mul hmq (inv_ne_zero hT0), P.ord_inv, hordT, hmord_eq q hmq]
            omega
          rw [StandardAnnulus.evalAt_eq_zero_of_ord_pos P
            (mul_ne_zero hmq (inv_ne_zero hT0)) hord2, map_zero]

  refine ⟨Q, hQC, hQP, haQ0, ?_⟩
  exact prox_eval_eq' N s hs0 μ hr P Q (hratall P) (hratall Q) T haQ0 hgmemQ hSpos hγval hβval

end FSlot
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

open Classical AlgebraicCurve.ReductionGraph IsLocalRing in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in

private theorem exists_const_abs_regularized_sub_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (pf : CoveringProfile) :
    ∃ C : ℝ, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean μ →
        (∀ y, y ∈ A ↔ μ y ≤ 1) → μ (p : AlgebraicClosure ℚ) < 1 →
        ∀ Γ : AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
          (p : AlgebraicClosure ℚ) s μ,
        ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ u : modularFunctionFieldBar N,
          P.ord u = 1 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord u) →
            |((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) - cfun Γ u
                - (Real.log (⨆ q : Fin r × Fin r,
                      μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
                    - 2 * Real.log (⨆ i, μ (evalVec s P i)))|
              ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  obtain ⟨C, hC⟩ := exists_const_abs_kernel_sub_prox_le N s hs p hp pf
  refine ⟨C, ?_⟩
  intro A hAp μ hμ hball hμp Γ P u hu D hD
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hratall : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational :=
    fun w => OfTopTransport.isRational_of_deg_eq_one w (deg_eq_one_modularFunctionFieldBar N w)
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨q₀, hq₀⟩ := exists_regVal_chord_ne_zero N s hs P hu
  have hr : 0 < r := q₀.1.pos
  have hs0 : ∀ j, s j ≠ 0 := fun j => hs.1.ne_zero j
  rcases Γ.partition P with ⟨i, hPi, -, -⟩ | ⟨e, hPe, -, -⟩
  ·
    obtain ⟨hTm, hTres, hTord1, hTpos, hTsep⟩ := Γ.disc i P hPi
    set T : modularFunctionFieldBar N := Γ.T i ((Γ.chart i).placeMap P)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
          (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))) with hTdef
    have hT0 : T ≠ 0 := (Γ.chart i).coe_ne_zero_of_residue_ne_zero hTres
    have hordT : P.ord T = 1 :=
      (Γ.chart i).ord_eq_one_of_disc hPi hTm hTres hTord1 hTpos hTsep
    have hPT0 : P.evalAt T = 0 :=
      StandardAnnulus.evalAt_eq_zero_of_ord_pos P hT0 (by rw [hordT]; exact one_pos)
    have hratdom : ∀ w ∈ (Γ.chart i).dom, w.IsRational := fun w _ => hratall w

    have hTglob_memP : Γ.T i ((Γ.chart i).placeMap P) ∈ P.toValuationSubring := by
      have h1 : Γ.T i ((Γ.chart i).placeMap P)
          = T + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))) := by
        rw [hTdef]; ring
      rw [h1]
      exact add_mem (GaussReduction.mem_of_ord_nonneg_gen P hT0 (by rw [hordT]; omega))
        (P.algebraMap_mem' _)

    have hfibT : ∀ w ∈ (Γ.chart i).dom, (Γ.chart i).placeMap w = (Γ.chart i).placeMap P →
        T ∈ w.toValuationSubring := by
      intro w hw hwpm
      by_cases hwP : w = P
      · rw [hwP]
        exact GaussReduction.mem_of_ord_nonneg_gen P hT0 (by rw [hordT]; omega)
      · exact GaussReduction.mem_of_ord_nonneg_gen w hT0 (hTsep w hw hwpm hwP).ge

    have hdiscP : ∀ w ∈ (Γ.chart i).dom,
        (Γ.chart i).placeMap w = (Γ.chart i).placeMap P →
        ∃ h : Γ.T i ((Γ.chart i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (w.evalAt (Γ.T i ((Γ.chart i).placeMap P))) ∈ (Γ.chart i).integers,
          (Γ.chart i).residue ⟨_, h⟩ ≠ 0 ∧
          ((Γ.chart i).placeMap w).ord ((Γ.chart i).residue ⟨_, h⟩) = 1 ∧
          0 < w.ord (Γ.T i ((Γ.chart i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (w.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) ∧
          ∀ Q ∈ (Γ.chart i).dom, (Γ.chart i).placeMap Q = (Γ.chart i).placeMap w → Q ≠ w →
            Q.ord (Γ.T i ((Γ.chart i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                  (w.evalAt (Γ.T i ((Γ.chart i).placeMap P)))) = 0 := by
      intro w hw hmap
      have h := Γ.disc i w hw
      have hTT : Γ.T i ((Γ.chart i).placeMap w) = Γ.T i ((Γ.chart i).placeMap P) := by
        rw [hmap]
      rw [hTT] at h
      exact h

    have hvalQ : ∀ Q ∈ (Γ.chart i).dom, (Γ.chart i).placeMap Q = (Γ.chart i).placeMap P →
        Q ≠ P → Q.evalAt T = Q.evalAt (Γ.T i ((Γ.chart i).placeMap P))
          - P.evalAt (Γ.T i ((Γ.chart i).placeMap P)) := by
      intro Q hQ hQpm hQP
      have hTmemQ : T ∈ Q.toValuationSubring :=
        GaussReduction.mem_of_ord_nonneg_gen Q hT0 (hTsep Q hQ hQpm hQP).ge
      have hTglob_memQ : Γ.T i ((Γ.chart i).placeMap P) ∈ Q.toValuationSubring := by
        have h1 : Γ.T i ((Γ.chart i).placeMap P)
            = T + algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
                (P.evalAt (Γ.T i ((Γ.chart i).placeMap P))) := by
          rw [hTdef]; ring
        rw [h1]
        exact add_mem hTmemQ (Q.algebraMap_mem' _)
      rw [hTdef, GaussReduction.evalAt_sub_of_mem Q (hratall Q) hTglob_memQ
        (Q.algebraMap_mem' _), GaussReduction.evalAt_algebraMap_const Q (hratall Q)]

    obtain ⟨Q, ⟨hQdom, hQpm⟩, hQP, haQ0, hprox⟩ := exists_Q_prox' N s hs μ P hr T hT0 hordT
      (fun Q => Q ∈ (Γ.chart i).dom ∧ (Γ.chart i).placeMap Q = (Γ.chart i).placeMap P)
      (by
        intro f hf hford
        obtain ⟨ε, hε, hlaw⟩ := abv_evalAt_eq_of_fibre' (Γ.chart i) μ Γ.hna Γ.ball hratdom
          hPi (Γ.T i ((Γ.chart i).placeMap P)) hdiscP hf hford
        refine ⟨ε, hε, ?_⟩
        rintro Q ⟨hQ, hQpm⟩ hQT0 hQTlt
        have hQP : Q ≠ P := by
          intro h
          rw [h, hPT0] at hQT0
          exact hQT0 rfl
        have hdict := hvalQ Q hQ hQpm hQP
        refine hlaw Q hQ hQpm ?_ ?_
        · rw [← sub_ne_zero, ← hdict]
          exact hQT0
        · rw [show Q.evalAt (Γ.T i ((Γ.chart i).placeMap P))
              - P.evalAt (Γ.T i ((Γ.chart i).placeMap P)) = Q.evalAt T from hdict.symm]
          exact hQTlt)
      (by
        intro δ hδ
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hμp
        set a : AlgebraicClosure ℚ := ((p : ℕ) : AlgebraicClosure ℚ) ^ (n + 1) with ha
        have ha0 : a ≠ 0 := pow_ne_zero _ hp0
        have haμ : μ a < δ := by
          rw [ha, map_pow, pow_succ]
          have h1 : μ ((p : ℕ) : AlgebraicClosure ℚ) ^ n * μ ((p : ℕ) : AlgebraicClosure ℚ)
              ≤ μ ((p : ℕ) : AlgebraicClosure ℚ) ^ n * 1 :=
            mul_le_mul_of_nonneg_left hμp.le (pow_nonneg (μ.nonneg _) n)
          rw [mul_one] at h1
          exact lt_of_le_of_lt h1 hn
        have haμ1 : μ a < 1 := by
          rw [ha, map_pow, pow_succ]
          have h1 : μ ((p : ℕ) : AlgebraicClosure ℚ) ^ n ≤ 1 :=
            pow_le_one₀ (μ.nonneg _) hμp.le
          nlinarith [μ.pos hp0, pow_nonneg (μ.nonneg ((p : ℕ) : AlgebraicClosure ℚ)) n]
        have haA : a ∈ A := hball a |>.mpr haμ1.le
        have hamax : (⟨a, haA⟩ : A) ∈ maximalIdeal A :=
          (mem_maximalIdeal_iff_abv_lt_one' μ hball haA).mpr haμ1
        obtain ⟨Q, hQdom, hQpm, hQval⟩ := (Γ.chart i).exists_mem_fibre_evalAt_eq hratdom hPi
          hTm hTres hTord1 hfibT haA hamax
        exact ⟨Q, ⟨hQdom, hQpm⟩, by rw [hQval]; exact ha0, by rw [hQval]; exact haμ⟩)
      (by
        rintro Q ⟨hQ, hQpm⟩ hQT0
        have hQP : Q ≠ P := by
          intro h
          rw [h, hPT0] at hQT0
          exact hQT0 rfl
        exact hTsep Q hQ hQpm hQP)

    have hker : kernel Γ P Q
        = groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i - Real.log (μ (Q.evalAt T)) := by
      have hdict := hvalQ Q hQdom hQpm hQP
      rw [kernel_eq, Γ.retract_of_mem_chart hPi, Γ.retract_of_mem_chart hQdom,
        pairPotential_inl_inl, localTerm_of_mem_chart Γ hPi, if_pos ⟨hQdom, hQpm⟩]
      have h1 : P.evalAt (Γ.T i ((Γ.chart i).placeMap P))
          - Q.evalAt (Γ.T i ((Γ.chart i).placeMap P)) = -(Q.evalAt T) := by
        rw [hdict]; ring
      rw [h1, μ.map_neg]
      ring
    exact abs_bracket_le_of_Q N s hs p hp pf A hAp μ hμ hball hμp Γ P u hu D hD T hT0 hordT
      (groundPotential Γ.src Γ.tgt Γ.len Γ.cuspIdx i i)
      (fun D' hD' => sum_erase_mul_kernel_disc Γ hPi D' hD') Q hQP hker hprox C
      (hC A hAp μ hμ hball hμp Γ P Q (Ne.symm hQP))
  ·
    set z : modularFunctionFieldBar N := (Γ.an e).param with hz
    set T : modularFunctionFieldBar N := z
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt z) with hTdef
    have hordT : P.ord T = 1 := (Γ.an e).ord_param_sub P hPe
    have hT0 : T ≠ 0 := by
      intro h0
      rw [h0, Place.ord_zero] at hordT
      exact zero_ne_one hordT
    have hPT0 : P.evalAt T = 0 :=
      StandardAnnulus.evalAt_eq_zero_of_ord_pos P hT0 (by rw [hordT]; exact one_pos)

    have hvalQ : ∀ Q ∈ (Γ.an e).dom, Q.evalAt T = Q.evalAt z - P.evalAt z := by
      intro Q hQ
      obtain ⟨hQrat, hQz, -, -, -⟩ := (Γ.an e).mem_dom Q hQ
      rw [hTdef, GaussReduction.evalAt_sub_of_mem Q hQrat hQz (Q.algebraMap_mem' _),
        GaussReduction.evalAt_algebraMap_const Q hQrat]

    obtain ⟨Q, ⟨hQdom, hQlev⟩, hQP, haQ0, hprox⟩ := exists_Q_prox' N s hs μ P hr T hT0 hordT
      (fun Q => Q ∈ (Γ.an e).dom ∧ μ (Q.evalAt z) = μ (P.evalAt z))
      (by
        intro f hf hford
        obtain ⟨ε, hε, hlaw⟩ := abv_evalAt_eq_of_level' (Γ.attached e).1 μ Γ.hna Γ.ball
          hPe hf hford
        refine ⟨ε, hε, ?_⟩
        rintro Q ⟨hQ, hQlev⟩ hQT0 hQTlt
        have hdict := hvalQ Q hQ
        refine hlaw Q hQ hQlev ?_ ?_
        · rw [← sub_ne_zero, ← hdict]
          exact hQT0
        · rw [show Q.evalAt z - P.evalAt z = Q.evalAt T from hdict.symm]
          exact hQTlt)
      (by
        intro δ hδ
        obtain ⟨Q, hQdom, hQzne, hQlev, hQlt⟩ := exists_same_level_abv_sub_lt' (Γ.an e) μ
          Γ.hna Γ.ball hPe hp0 hμp hδ
        have hdict := hvalQ Q hQdom
        refine ⟨Q, ⟨hQdom, hQlev⟩, ?_, ?_⟩
        · rw [hdict]
          exact sub_ne_zero.mpr hQzne
        · rw [hdict]
          exact hQlt)
      (by
        rintro Q ⟨hQ, -⟩ hQT0
        have hQP : Q ≠ P := by
          intro h
          rw [h, hPT0] at hQT0
          exact hQT0 rfl
        exact ord_param_sub_eq_zero_of_ne' (Γ.an e) hPe hQ hQP)

    have hker : kernel Γ P Q = kernel Γ P P - Real.log (μ (Q.evalAt T)) := by
      have hdict := hvalQ Q hQdom
      have hrQ := Γ.retract_of_mem_an hQdom
      have hrP := Γ.retract_of_mem_an hPe
      rw [kernel_eq (P := P) (Q := Q), kernel_eq (P := P) (Q := P), hrQ, hrP, hQlev,
        localTerm_of_mem_an Γ hPe (Q := Q), localTerm_of_mem_an Γ hPe (Q := P),
        if_pos hQdom, if_pos hPe, sub_self, map_zero, Real.log_zero, neg_zero]
      have h1 : P.evalAt z - Q.evalAt z = -(Q.evalAt T) := by
        rw [hdict]; ring
      rw [h1, μ.map_neg, hQlev]
      ring
    exact abs_bracket_le_of_Q N s hs p hp pf A hAp μ hμ hball hμp Γ P u hu D hD T hT0 hordT
      (kernel Γ P P)
      (fun D' hD' => sum_erase_mul_kernel_an' N s hs p hp pf A hAp μ Γ.hna Γ.ball hμp Γ
        hPe D' hD') Q hQP hker hprox C
      (hC A hAp μ hμ hball hμp Γ P Q (Ne.symm hQP))

section CuspPairing

variable {pf : CoveringProfile} {A : ValuationSubring (AlgebraicClosure ℚ)}
  {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
  {P₀ : Place (AlgebraicClosure ℚ) F} {p : AlgebraicClosure ℚ}
  {r : ℕ} {s : Fin r → F} {μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ}

private theorem sum_erase_add (Γ : AdaptedCovering pf A F P₀ p s μ) (P : Place (AlgebraicClosure ℚ) F)
    (D₁ D₂ : Divisor (AlgebraicClosure ℚ) F) :
    (((D₁ + D₂).erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
      = ((D₁.erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
        + ((D₂.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) := by
  rw [Finsupp.erase_add, Finsupp.sum_add_index' (fun w => by simp) (fun w b₁ b₂ => by push_cast; ring)]

private theorem sum_erase_zsmul (Γ : AdaptedCovering pf A F P₀ p s μ) (P : Place (AlgebraicClosure ℚ) F)
    (m : ℤ) (D : Divisor (AlgebraicClosure ℚ) F) :
    (((m • D).erase P).sum fun w n => (n : ℝ) * kernel Γ P w)
      = (m : ℝ) * ((D.erase P).sum fun w n => (n : ℝ) * kernel Γ P w) := by
  classical
  have h : (m • D).erase P = m • D.erase P := by
    ext w
    by_cases hw : w = P
    · subst hw
      rw [Finsupp.smul_apply, Finsupp.erase_same, Finsupp.erase_same, smul_zero]
    · rw [Finsupp.smul_apply, Finsupp.erase_ne hw, Finsupp.erase_ne hw, Finsupp.smul_apply]
  rw [h, Finsupp.sum_smul_index' (fun w => by simp)]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by simp only [smul_eq_mul, Int.cast_mul]; ring

private theorem cfun_one (Γ : AdaptedCovering pf A F P₀ p s μ) : cfun Γ (1 : F) = 0 := by
  have h := cfun_mul Γ (one_ne_zero (α := F)) one_ne_zero
  rw [mul_one] at h
  linarith

private theorem cfun_inv (Γ : AdaptedCovering pf A F P₀ p s μ) {u : F} (hu : u ≠ 0) : cfun Γ u⁻¹ = -cfun Γ u := by
  have h := cfun_mul Γ hu (inv_ne_zero hu)
  rw [mul_inv_cancel₀ hu, cfun_one] at h
  linarith

private theorem cfun_pow (Γ : AdaptedCovering pf A F P₀ p s μ) {u : F} (hu : u ≠ 0) (n : ℕ) :
    cfun Γ (u ^ n) = (n : ℝ) * cfun Γ u := by
  induction n with
  | zero => rw [pow_zero, cfun_one]; simp
  | succ n ih =>
    rw [pow_succ, cfun_mul Γ (pow_ne_zero n hu) hu, ih]
    push_cast
    ring

private theorem cfun_zpow (Γ : AdaptedCovering pf A F P₀ p s μ) {u : F} (hu : u ≠ 0) (m : ℤ) :
    cfun Γ (u ^ m) = (m : ℝ) * cfun Γ u := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, cfun_pow Γ hu n]
    push_cast
    ring
  · rw [zpow_neg, zpow_natCast, cfun_inv Γ (pow_ne_zero n hu), cfun_pow Γ hu n]
    push_cast
    ring

end CuspPairing
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

private theorem exists_abs_log_ciSup_abv_le {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℕ} (hp : p.Prime)
    (a : ι → AlgebraicClosure ℚ) (h0 : ∃ i, a i ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
        |Real.log (⨆ i, μ (a i))| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  have hF : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 → a i ≠ 0 →
        |Real.log (μ (a i))| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
    intro i
    by_cases hi : a i = 0
    · exact ⟨0, le_rfl, fun μ _ _ h => absurd hi h⟩
    · obtain ⟨C, hC0, hC⟩ := FixedAlgebraic.exists_abs_log_abv_le hp (a i) hi
      exact ⟨C, hC0, fun μ hμ hμp _ => hC μ hμ hμp⟩
  choose C hC0 hC using hF
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun μ hμ hμp => ?_⟩
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) :=
    neg_nonneg.mpr (Real.log_nonpos (μ.nonneg _) hμp.le)
  obtain ⟨i₀, hi₀⟩ := h0
  obtain ⟨i₁, hi₁⟩ := exists_eq_ciSup_of_finite (f := fun i => μ (a i))
  have hbdd : BddAbove (Set.range fun i => μ (a i)) := (Set.finite_range _).bddAbove
  have hpos : 0 < ⨆ i, μ (a i) := lt_of_lt_of_le (μ.pos hi₀) (le_ciSup hbdd i₀)
  have ha1 : a i₁ ≠ 0 := by
    intro h
    have h' : μ (a i₁) = 0 := by rw [h, map_zero]
    rw [hi₁] at h'
    rw [h'] at hpos
    exact lt_irrefl _ hpos
  rw [← hi₁]
  calc |Real.log (μ (a i₁))| ≤ C i₁ * (-Real.log (μ (p : AlgebraicClosure ℚ))) := hC i₁ μ hμ hμp ha1
    _ ≤ (∑ i, C i) * (-Real.log (μ (p : AlgebraicClosure ℚ))) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ i₁)) hlam

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
open Classical in

private theorem exists_const_abs_cuspPairing_sub_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (p : ℕ) (hp : p.Prime) (pf : CoveringProfile) :
    ∃ C : ℝ, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean μ →
        (∀ y, y ∈ A ↔ μ y ≤ 1) → μ (p : AlgebraicClosure ℚ) < 1 →
        ∀ Γ : AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N)
          (p : AlgebraicClosure ℚ) s μ,
        ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord t) →
          |((D.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) - cfun Γ t|
            ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hrat : (cuspInftyBar N).IsRational := EmbSeparation.isRational N (cuspInftyBar N)

  by_cases ht : t = 0
  · refine ⟨0, fun A hA μ hμ hball hμp Γ D hD => ?_⟩
    have hD0 : D = 0 := Finsupp.ext fun w => by simp [hD w, ht]
    have h0 : ((D.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) - cfun Γ t
        = 0 := by
      rw [hD0, ht, Finsupp.erase_zero, Finsupp.sum_zero_index]
      unfold cfun
      rw [ComponentChart.logGaussNorm_zero, sub_zero]
    rw [h0]
    simp

  obtain ⟨u₀, hu₀⟩ := EmbSeparation.exists_ord_eq_one (cuspInftyBar N)
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hu₀
    exact zero_ne_one hu₀
  set m : ℤ := (cuspInftyBar N).ord t with hm
  set v : modularFunctionFieldBar N := t * (u₀ ^ m)⁻¹ with hv
  have hum0 : u₀ ^ m ≠ 0 := zpow_ne_zero m hu₀0
  have hv0 : v ≠ 0 := mul_ne_zero ht (inv_ne_zero hum0)
  have htv : t = v * u₀ ^ m := by rw [hv, inv_mul_cancel_right₀ hum0]
  have hordv : (cuspInftyBar N).ord v = 0 := by
    rw [hv, (cuspInftyBar N).ord_mul ht (inv_ne_zero hum0), (cuspInftyBar N).ord_inv,
      (cuspInftyBar N).ord_zpow, hu₀, mul_one, ← hm, add_neg_cancel]
  have hval : (cuspInftyBar N).evalAt v ≠ 0 :=
    StandardAnnulus.evalAt_ne_zero_of_ord_eq_zero (cuspInftyBar N) hrat hv0 hordv
  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) u₀ hu₀0
  obtain ⟨Dv, hDv, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) v hv0
  have hDv0 : Dv (cuspInftyBar N) = 0 := by rw [hDv, hordv]

  obtain ⟨Cf, hCf⟩ := exists_const_abs_regularized_sub_le N s hs p hp pf
  haveI : Nonempty (Fin r × Fin r) :=
    ⟨(⟨0, EmbSeparation.pos_of_isEmbBasis hs⟩, ⟨0, EmbSeparation.pos_of_isEmbBasis hs⟩)⟩
  haveI : Nonempty (Fin r) := ⟨⟨0, EmbSeparation.pos_of_isEmbBasis hs⟩⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_log_ciSup_abv_le hp
    (fun q : Fin r × Fin r => regVal s (cuspInftyBar N) u₀ 1 1
      (evalVec s (cuspInftyBar N) q.1 • s q.2 - evalVec s (cuspInftyBar N) q.2 • s q.1))
    (exists_regVal_chord_ne_zero N s hs (cuspInftyBar N) hu₀)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_log_ciSup_abv_le hp (evalVec s (cuspInftyBar N))
    ⟨pivotIndex s (cuspInftyBar N) (EmbSeparation.pos_of_isEmbBasis hs), by
      rw [EmbSeparation.evalVec_pivot hs (cuspInftyBar N)]; exact one_ne_zero⟩
  obtain ⟨C₃, hC₃0, hC₃⟩ := FixedAlgebraic.exists_abs_log_abv_le hp ((cuspInftyBar N).evalAt v) hval
  refine ⟨|(m : ℝ)| * (|Cf| + C₁ + 2 * C₂) + C₃, fun A hA μ hμ hball hμp Γ D hD => ?_⟩
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlam : 0 ≤ (-Real.log (μ (p : AlgebraicClosure ℚ))) := neg_nonneg.mpr (Real.log_nonpos (μ.nonneg _) hμp.le)

  have hDeq : D = m • D₀ + Dv := by
    ext w
    rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hD w, hD₀ w, hDv w, htv,
      w.ord_mul hv0 hum0, w.ord_zpow]
    ring

  have hR : ((D.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) = (m : ℝ) * ((D₀.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) + ((Dv.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) := by
    rw [hDeq, sum_erase_add, sum_erase_zsmul]
  have hRv : ((Dv.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) = -Real.log (μ ((cuspInftyBar N).evalAt v)) + cfun Γ v := by
    rw [Finsupp.erase_of_notMem_support (by rw [Finsupp.mem_support_iff, not_not]; exact hDv0)]
    exact kernel_green N s hs p hp pf A hA μ hμ hball hμp Γ v hv0 Dv hDv (cuspInftyBar N) hDv0
  have hf := hCf A hA μ hμ hball hμp Γ (cuspInftyBar N) u₀ hu₀ D₀ hD₀
  have hct : cfun Γ t = cfun Γ v + (m : ℝ) * cfun Γ u₀ := by
    rw [htv, cfun_mul Γ hv0 hum0, cfun_zpow Γ hu₀0]
  have h1 := hC₁ μ hμ hμp
  have h2 := hC₂ μ hμ hμp
  have h3 := hC₃ μ hμ hμp

  rw [hR, hRv, hct]
  have hkey : (m : ℝ) * ((D₀.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) + (-Real.log (μ ((cuspInftyBar N).evalAt v)) + cfun Γ v)
      - (cfun Γ v + (m : ℝ) * cfun Γ u₀)
      = (m : ℝ) * (((D₀.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) - cfun Γ u₀
          - (Real.log (⨆ q : Fin r × Fin r, μ (regVal s (cuspInftyBar N) u₀ 1 1
              (evalVec s (cuspInftyBar N) q.1 • s q.2 - evalVec s (cuspInftyBar N) q.2 • s q.1)))
            - 2 * Real.log (⨆ i, μ (evalVec s (cuspInftyBar N) i))))
        + (m : ℝ) * (Real.log (⨆ q : Fin r × Fin r, μ (regVal s (cuspInftyBar N) u₀ 1 1
              (evalVec s (cuspInftyBar N) q.1 • s q.2 - evalVec s (cuspInftyBar N) q.2 • s q.1)))
            - 2 * Real.log (⨆ i, μ (evalVec s (cuspInftyBar N) i)))
        + -Real.log (μ ((cuspInftyBar N).evalAt v)) := by ring
  rw [hkey]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_neg]
  have hA1 : |(m : ℝ)| * |((D₀.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * kernel Γ (cuspInftyBar N) w) - cfun Γ u₀
      - (Real.log (⨆ q : Fin r × Fin r, μ (regVal s (cuspInftyBar N) u₀ 1 1
          (evalVec s (cuspInftyBar N) q.1 • s q.2 - evalVec s (cuspInftyBar N) q.2 • s q.1)))
        - 2 * Real.log (⨆ i, μ (evalVec s (cuspInftyBar N) i)))|
      ≤ |(m : ℝ)| * (|Cf| * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by
    refine mul_le_mul_of_nonneg_left (hf.trans ?_) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_abs_self Cf) hlam
  have hA2 : |(m : ℝ)| * |Real.log (⨆ q : Fin r × Fin r, μ (regVal s (cuspInftyBar N) u₀ 1 1
          (evalVec s (cuspInftyBar N) q.1 • s q.2 - evalVec s (cuspInftyBar N) q.2 • s q.1)))
        - 2 * Real.log (⨆ i, μ (evalVec s (cuspInftyBar N) i))|
      ≤ |(m : ℝ)| * ((C₁ + 2 * C₂) * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_two]
    linarith
  linarith [hA1, hA2, h3]

private theorem exists_kernel_of_adaptedCovering (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (p : ℕ) (hp : p.Prime) (pf : CoveringProfile) :
    ∃ C : ℝ, ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
      ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean μ →
        (∀ y, y ∈ A ↔ μ y ≤ 1) → μ (p : AlgebraicClosure ℚ) < 1 →
        AdaptedCovering pf A (modularFunctionFieldBar N) (cuspInftyBar N) (p : AlgebraicClosure ℚ) s μ →
      ∃ (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
            Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
        (c : modularFunctionFieldBar N → ℝ),
        (∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂) ∧
        (∀ f : modularFunctionFieldBar N, f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
          ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
            (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f) ∧
        (∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
          |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ i : Fin r, |c (s i)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord t) →
          |((D.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * g (cuspInftyBar N) w) - c t|
            ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ u : modularFunctionFieldBar N, P.ord u = 1 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord u) →
            |((D.erase P).sum fun w n => (n : ℝ) * g P w) - c u
                - (Real.log (⨆ q : Fin r × Fin r,
                      μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
                    - 2 * Real.log (⨆ i, μ (evalVec s P i)))|
              ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → f₁ + f₂ ≠ 0 →
          c (f₁ + f₂) ≤ max (c f₁) (c f₂)) := by
  obtain ⟨C₃, h₃⟩ := exists_const_abs_kernel_sub_prox_le N s hs p hp pf
  obtain ⟨C₅, h₅⟩ := exists_const_abs_cuspPairing_sub_le N s hs t p hp pf
  obtain ⟨C₆, h₆⟩ := exists_const_abs_regularized_sub_le N s hs p hp pf
  refine ⟨max (max C₃ (pf.B : ℝ)) (max C₅ C₆), ?_⟩
  intro A hA μ hμ hball hμp Γ
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hμpos : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hlam : 0 ≤ -Real.log (μ (p : AlgebraicClosure ℚ)) :=
    neg_nonneg.mpr (Real.log_nonpos hμpos.le hμp.le)
  refine ⟨kernel Γ, cfun Γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f₁ f₂ h₁ h₂
    exact cfun_mul Γ h₁ h₂
  · intro f hf D hD P hP
    exact kernel_green N s hs p hp pf A hA μ hμ hball hμp Γ f hf D hD P hP
  · intro P Q hPQ
    exact (h₃ A hA μ hμ hball hμp Γ P Q hPQ).trans
      (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) hlam)
  · intro i
    exact (abs_cfun_le Γ hμpos i).trans
      (mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) hlam)
  · intro D hD
    exact (h₅ A hA μ hμ hball hμp Γ D hD).trans
      (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) hlam)
  · intro P u hu D hD
    exact (h₆ A hA μ hμ hball hμp Γ P u hu D hD).trans
      (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) hlam)
  · intro f₁ f₂ h₁ h₂ h₁₂
    exact cfun_add_le Γ h₁ h₂ h₁₂

end HarmonicGlue
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.AdaptedCovering P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ComponentChart P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.SimpleGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph.adjGraph P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le.AlgebraicCurve.ReductionGraph"

theorem solution (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (p : ℕ) (hp : p.Prime) :
    ∃ C : ℝ, ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
      ∃ (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
            Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
        (c : modularFunctionFieldBar N → ℝ),
        (∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂) ∧
        (∀ f : modularFunctionFieldBar N, f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
          ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
            (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f) ∧
        (∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
          |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ i : Fin r, |c (s i)| ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord t) →
          |((D.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * g (cuspInftyBar N) w) - c t|
            ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ u : modularFunctionFieldBar N, P.ord u = 1 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord u) →
            |((D.erase P).sum fun w n => (n : ℝ) * g P w) - c u
                - (Real.log (⨆ q : Fin r × Fin r,
                      μ (regVal s P u 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
                    - 2 * Real.log (⨆ i, μ (evalVec s P i)))|
              ≤ C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → f₁ + f₂ ≠ 0 →
          c (f₁ + f₂) ≤ max (c f₁) (c f₂)) := by
  obtain ⟨pf, hpf⟩ :=
    ModularCurve.exists_profile_forall_nonempty_adaptedCovering_of_isEmbBasis N hN hN5 s hs p hp
  obtain ⟨C, hcore⟩ := HarmonicGlue.exists_kernel_of_adaptedCovering N s hs t p hp pf
  refine ⟨C, fun μ hμ hμp => ?_⟩
  obtain ⟨A, hball, hAp⟩ := HarmonicGlue.exists_valuationSubring_ball μ hμ p hp hμp
  obtain ⟨Γ⟩ := hpf A hAp μ hμ hball
  exact hcore A hAp μ hμ hball hμp Γ

#print axioms solution

end S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_exists_greenKernel_regularizedAt_ultrametric_of_prime_of_five_le (solution)
