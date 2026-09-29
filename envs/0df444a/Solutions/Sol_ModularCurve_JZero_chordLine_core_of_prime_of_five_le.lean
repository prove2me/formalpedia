-- Prove2me | solution 1 for ModularCurve.JZero.chordLine_core_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/26909175-48f7-5eee-bece-6d022e19ed4d

import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_quot_rep
import Theorems.Thm_ModularCurve_JZero_chordLine_section_ledger_of_prime_of_five_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_chordLine_core_of_prime_of_five_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.MultCovering.instAlgebraFbar ModularCurve.MultCovering.instFieldFbar ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.LevelOnePhi.instAddCommGroup instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.MultCovering.ssValue_edgeOf ModularCurve.MultCovering.ChartCtx.mk.sizeOf_spec ModularCurve.MultCovering.ChartCtx.mk.injEq ModularCurve.MultCovering.chart_one ModularCurve.MultCovering.chart_zero AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.MultCovering.AnnCtx.mk.sizeOf_spec ModularCurve.MultCovering.AnnCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.sizeOf_spec ModularCurve.MultCovering.FamCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.MultCovering.FamCtx.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_chordLine_core_of_prime_of_five_le.ModularCurve AlgebraicCurve"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis cuspInftyBar modularFunctionFieldBar JZero hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar JZero.quot_rep JZero.chordLine_section_ledger_of_prime_of_five_le"
p2m_open "ModularCurve"

namespace JZero p2m_export "ModularCurve.JZero" "quot_rep chordLine_section_ledger_of_prime_of_five_le" end JZero
p2m_open_scoped "ModularCurve.JZero" in
private theorem JZero.coeffSum_eq_zero_of_ord (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N)
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hA : ∀ w, A w = w.ord f) :
    (A.sum fun _ m => (m : ℝ)) = 0 := by
  by_cases hf : f = 0
  · have hA0 : A = 0 := Finsupp.ext fun w => by
      rw [hA w, hf, Place.ord_zero]
      simp
    rw [hA0]
    simp
  · haveI hpd : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
    obtain ⟨D, hD, hdeg⟩ := hpd.exists_divisor f hf
    have hAD : A = D := Finsupp.ext fun w => by rw [hA w, hD w]
    have hdegA : Divisor.degree A = 0 := by rw [hAD]; exact hdeg
    have h1 : Divisor.degree A = A.sum fun v n => n * (v.deg : ℤ) := rfl
    have h2 : (A.sum fun v n => n * (v.deg : ℤ)) = A.sum fun _ n => n := by
      simp only [Finsupp.sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N w]
      simp
    have h3 : (A.sum fun _ n => n) = (0 : ℤ) := by rw [← h2, ← h1]; exact hdegA
    have h4 : (A.sum fun _ m => (m : ℝ)) = ((A.sum fun _ n => n : ℤ) : ℝ) := by
      simp only [Finsupp.sum]
      push_cast
      rfl
    rw [h4, h3, Int.cast_zero]

end ModularCurve

namespace CoreObj

private theorem coeffSum_eq_zero_of_ord_int (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hA : ∀ w, A w = w.ord f) :
    (A.sum fun _ m => m) = 0 := by
  have _ := hf
  have h := ModularCurve.JZero.coeffSum_eq_zero_of_ord N f A hA
  have h4 : (A.sum fun _ m => (m : ℝ)) = ((A.sum fun _ n => n : ℤ) : ℝ) := by
    simp only [Finsupp.sum]
    push_cast
    rfl
  rw [h4] at h
  exact_mod_cast h

open Classical in

private def Y (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  (((B.erase v).erase (cuspInftyBar N)).sum fun w m => (m : ℝ) *
      (absLogHeight (fun p : Fin r × Fin r =>
          w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
        - absLogHeight (fun p : Fin r × Fin r =>
            w.evalAt (evalVec s (cuspInftyBar N) p.1 • s p.2
              - evalVec s (cuspInftyBar N) p.2 • s p.1))))
    + ((B.erase v) (cuspInftyBar N) : ℝ) * absLogHeight (chordVec s v (cuspInftyBar N))

private theorem section_ledger (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        B v = 0 → v ≠ cuspInftyBar N →
        |Y N s v B - (k : ℝ) * (((embDivisor N).sum fun _ m => (m : ℝ)) - 1) * pointHt s v|
          ≤ C * (k + 1) := by
  have _ := ht
  simpa only [Y] using JZero.chordLine_section_ledger_of_prime_of_five_le N hN hN5 s hs

private theorem height_difference (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (_hs : IsEmbBasis N s)
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hA : ∀ w, A w = w.ord f)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (_hv : A v = 0) (_hvo : v ≠ cuspInftyBar N)
    (k : ℕ) (u₁ u₂ : modularFunctionFieldBar N)
    (_h₁ : u₁ ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (_h₂ : u₂ ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (hu₂ : u₂ ≠ 0) (_hv₂ : v.ord u₂ = 0) (hmul : f * u₂ = u₁)
    (B₁ B₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB₁ : ∀ w, B₁ w = w.ord u₁ + ((k : ℤ) • embDivisor N) w)
    (hB₂ : ∀ w, B₂ w = w.ord u₂ + ((k : ℤ) • embDivisor N) w) :
    Y N s v A = Y N s v B₁ - Y N s v B₂ := by
  classical
  have hordu₁ : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      w.ord u₁ = w.ord f + w.ord u₂ := fun w => by
    rw [← hmul]; exact w.ord_mul hf hu₂
  have hABf : A = B₁ - B₂ := Finsupp.ext fun w => by
    rw [Finsupp.sub_apply, hA w, hB₁ w, hB₂ w, hordu₁ w]; ring
  have herase : ∀ (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (z : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (D - E).erase z = D.erase z - E.erase z := fun D E z => Finsupp.ext fun w => by
    by_cases h : w = z <;> simp [h, Finsupp.sub_apply]
  simp only [Y, hABf, herase]
  rw [Finsupp.sum_sub_index (fun a b₁ b₂ => by push_cast; ring)]
  simp only [Finsupp.sub_apply]
  push_cast
  ring

private theorem exists_uniformiser (N : ℕ) [NeZero N] :
    ∃ t : modularFunctionFieldBar N, (cuspInftyBar N).ord t = 1 :=
  AlgebraicCurve.Place.exists_ord_eq_one (cuspInftyBar N)

set_option maxSynthPendingDepth 3 in

private theorem exists_divisor_of_section (N : ℕ) [NeZero N] (k : ℕ)
    (u : modularFunctionFieldBar N) (hu : u ≠ 0) :
    ∃ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w := by
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, _⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) u hu
  exact ⟨D + (k : ℤ) • embDivisor N, fun w => by
    rw [Finsupp.add_apply, hD w]⟩

private theorem chordLine_core (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      f ≠ 0 → (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), A v = 0 →
        |(((A.erase v).erase (cuspInftyBar N)).sum fun w m => (m : ℝ) *
            (absLogHeight (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
              - absLogHeight (fun p : Fin r × Fin r =>
                  w.evalAt (evalVec s (cuspInftyBar N) p.1 • s p.2 - evalVec s (cuspInftyBar N) p.2 • s p.1))))
          + ((A.erase v) (cuspInftyBar N) : ℝ)
              * absLogHeight (chordVec s v (cuspInftyBar N))|
        ≤ c * (A.sum fun _ m => |(m : ℝ)|) := by
  classical
  obtain ⟨t, ht⟩ := exists_uniformiser N
  obtain ⟨C₀, hE1⟩ := JZero.quot_rep N s hs
  obtain ⟨C, hCnn, hST1⟩ := section_ledger N hN hN5 s hs t ht
  refine ⟨2 * C * (max C₀ 0 + 2), ?_⟩
  intro f A hf hA v hv

  show |Y N s v A| ≤ _

  have hmass_nn : (0 : ℝ) ≤ A.sum fun _ m => |(m : ℝ)| :=
    Finsupp.sum_nonneg fun _ _ => abs_nonneg _
  rcases eq_or_ne A 0 with rfl | hA0
  ·
    simp [Y]
  rcases eq_or_ne v (cuspInftyBar N) with rfl | hvo
  ·
    have hY : Y N s (cuspInftyBar N) A = 0 := by
      simp [Y, sub_self, Finsupp.erase_same]
    rw [hY, abs_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCnn) (by positivity)) hmass_nn

  obtain ⟨k, u₁, u₂, hk, h₁, h₂, hu₂, hv₂, hmul⟩ := hE1 f A hf hA v hv hvo
  have hu₁ : u₁ ≠ 0 := by
    rw [← hmul]; exact mul_ne_zero hf hu₂
  obtain ⟨B₁, hB₁⟩ := exists_divisor_of_section N k u₁ hu₁
  obtain ⟨B₂, hB₂⟩ := exists_divisor_of_section N k u₂ hu₂

  have hembv : ((k : ℤ) • embDivisor N) v = 0 := by
    simp [embDivisor, hvo]
  have hB₂v : B₂ v = 0 := by rw [hB₂ v, hv₂, hembv]; ring
  have hB₁v : B₁ v = 0 := by
    have : v.ord u₁ = 0 := by
      rw [← hmul, v.ord_mul hf hu₂, hv₂, ← hA v, hv]; ring
    rw [hB₁ v, this, hembv]; ring

  have hdiff := height_difference N s hs f hf A hA v hv hvo k u₁ u₂ h₁ h₂ hu₂ hv₂ hmul B₁ B₂ hB₁ hB₂
  have hL₁ := hST1 k u₁ hu₁ h₁ B₁ hB₁ v hB₁v hvo
  have hL₂ := hST1 k u₂ hu₂ h₂ B₂ hB₂ v hB₂v hvo

  have htri : |Y N s v A| ≤ 2 * C * (k + 1) := by
    rw [hdiff]
    set P := (k : ℝ) * (((embDivisor N).sum fun _ m => (m : ℝ)) - 1) * pointHt s v with hP
    calc |Y N s v B₁ - Y N s v B₂|
        ≤ |Y N s v B₁ - P| + |P - Y N s v B₂| := abs_sub_le _ _ _
      _ = |Y N s v B₁ - P| + |Y N s v B₂ - P| := by rw [abs_sub_comm P]
      _ ≤ C * (k + 1) + C * (k + 1) := add_le_add hL₁ hL₂
      _ = 2 * C * (k + 1) := by ring

  have hmass_ge : (1 : ℝ) ≤ A.sum fun _ m => |(m : ℝ)| := by
    obtain ⟨w, hw⟩ : ∃ w, A w ≠ 0 := by
      by_contra h
      push Not at h
      exact hA0 (Finsupp.ext h)
    have hw' : w ∈ A.support := Finsupp.mem_support_iff.mpr hw
    have h1 : (1 : ℝ) ≤ |(A w : ℝ)| := by
      have : (1 : ℤ) ≤ |A w| := Int.one_le_abs hw
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ (|A w| : ℝ) := by exact_mod_cast this
        _ = |(A w : ℝ)| := by ring
    calc (1 : ℝ) ≤ |(A w : ℝ)| := h1
      _ ≤ A.support.sum fun w' => |(A w' : ℝ)| :=
          Finset.single_le_sum (f := fun w' => |(A w' : ℝ)|) (fun _ _ => abs_nonneg _) hw'
      _ = A.sum fun _ m => |(m : ℝ)| := rfl

  have hkb : (k : ℝ) + 1 ≤ (A.sum fun _ m => |(m : ℝ)|) + max C₀ 0 + 1 := by
    have : (k : ℝ) ≤ (A.sum fun _ m => |(m : ℝ)|) + C₀ := hk
    have h2 : C₀ ≤ max C₀ 0 := le_max_left _ _
    linarith
  calc |Y N s v A| ≤ 2 * C * (k + 1) := htri
    _ ≤ 2 * C * ((A.sum fun _ m => |(m : ℝ)|) + max C₀ 0 + 1) := by
        have h2C : (0 : ℝ) ≤ 2 * C := by linarith
        exact mul_le_mul_of_nonneg_left hkb h2C
    _ = 2 * C * (max C₀ 0 + 2) * (A.sum fun _ m => |(m : ℝ)|)
          - 2 * C * ((max C₀ 0 + 1) * ((A.sum fun _ m => |(m : ℝ)|) - 1)) := by ring
    _ ≤ 2 * C * (max C₀ 0 + 2) * (A.sum fun _ m => |(m : ℝ)|) := by
        have hm1 : (0 : ℝ) ≤ (A.sum fun _ m => |(m : ℝ)|) - 1 := by linarith
        have key : (0 : ℝ) ≤ 2 * C * ((max C₀ 0 + 1) * ((A.sum fun _ m => |(m : ℝ)|) - 1)) :=
          mul_nonneg (by linarith) (mul_nonneg (by positivity) hm1)
        linarith

end CoreObj

end

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_JZero_chordLine_core_of_prime_of_five_le.ModularCurve in
theorem solution (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c : ℝ, ∀ (f : modularFunctionFieldBar N)
      (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      f ≠ 0 → (∀ w, A w = w.ord f) →
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), A v = 0 →
        |(((A.erase v).erase (cuspInftyBar N)).sum fun w m => (m : ℝ) *
            (absLogHeight (fun p : Fin r × Fin r => w.evalAt (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
              - absLogHeight (fun p : Fin r × Fin r =>
                  w.evalAt (evalVec s (cuspInftyBar N) p.1 • s p.2 - evalVec s (cuspInftyBar N) p.2 • s p.1))))
          + ((A.erase v) (cuspInftyBar N) : ℝ)
              * absLogHeight (chordVec s v (cuspInftyBar N))|
        ≤ c * (A.sum fun _ m => |(m : ℝ)|) := by
  exact CoreObj.chordLine_core N hN hN5 s hs

end S_ModularCurve_JZero_chordLine_core_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_JZero_chordLine_core_of_prime_of_five_le (solution)
