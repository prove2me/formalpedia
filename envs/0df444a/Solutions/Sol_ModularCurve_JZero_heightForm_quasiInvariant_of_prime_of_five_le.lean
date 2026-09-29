-- Prove2me | solution 1 for ModularCurve.JZero.heightForm_quasiInvariant_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a8f4e6a6-840d-5be0-8133-de3e40c9bd19

import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_JZero_ptsum_pointHt_le_divNaiveHeight
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_pairing_principal_le_of_prime_of_five_le
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.MultCovering.instAlgebraFbar ModularCurve.MultCovering.instFieldFbar ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.LevelOnePhi.instAddCommGroup instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
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

set_option Elab.async false
set_option autoImplicit false

noncomputable section

namespace B0R1

open Finset

private def auxAbs {X : Type} (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ) (D : X →₀ ℤ) : ℝ :=
  ((γ : ℝ) + (D.sum fun _ n => (n : ℝ)) - 1) * (D.sum fun v n => (n : ℝ) * t v)
    - (∑ p ∈ D.support.offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * b p.1 p.2) / 2
    - (2 - 2 * (γ : ℝ)) * (D.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * t v)

private def pairOff {X : Type} [DecidableEq X] (b : X → X → ℝ) (A B : X →₀ ℤ) : ℝ :=
  ∑ p ∈ (A.support ∪ B.support).offDiag, ((A p.1 : ℝ) * (B p.2 : ℝ)) * b p.1 p.2

private def pairDiag {X : Type} [DecidableEq X] (t : X → ℝ) (A B : X →₀ ℤ) : ℝ :=
  ∑ v ∈ A.support ∪ B.support, ((A v : ℝ) * (B v : ℝ)) * t v

private def ePt {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ) (Q : X →₀ ℤ) (c : ℤ)
    (v : X) : ℝ :=
  (∑ w ∈ Q.support.erase v, (Q w : ℝ) * (t w - b v w))
    + (2 * (γ : ℝ) - 1) * (Q v : ℝ) * t v - (c : ℝ) * t v

private def phiC {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ) (Q : X →₀ ℤ) (c : ℤ)
    (A : X →₀ ℤ) : ℝ :=
  ∑ v ∈ A.support, (A v : ℝ) * ePt γ t b Q c v

private theorem sum_ext_weight {X : Type} (A : X →₀ ℤ) (g : X → ℝ) {U : Finset X}
    (hA : A.support ⊆ U) :
    (A.sum fun v n => (n : ℝ) * g v) = ∑ v ∈ U, (A v : ℝ) * g v :=
  Finsupp.sum_of_support_subset A hA _ (by simp)

private theorem sum_ext_deg {X : Type} (A : X →₀ ℤ) {U : Finset X} (hA : A.support ⊆ U) :
    (A.sum fun _ n => (n : ℝ)) = ∑ v ∈ U, (A v : ℝ) :=
  Finsupp.sum_of_support_subset A hA _ (by simp)

private theorem sum_ext_selfpair {X : Type} (A : X →₀ ℤ) (g : X → ℝ) {U : Finset X}
    (hA : A.support ⊆ U) :
    (A.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * g v)
      = ∑ v ∈ U, ((A v : ℝ) * ((A v : ℝ) - 1) / 2) * g v :=
  Finsupp.sum_of_support_subset A hA _ (by simp)

private theorem pairOff_ext {X : Type} [DecidableEq X] (b : X → X → ℝ) (A B : X →₀ ℤ)
    {U : Finset X} (hA : A.support ⊆ U) (hB : B.support ⊆ U) :
    pairOff b A B = ∑ p ∈ U.offDiag, ((A p.1 : ℝ) * (B p.2 : ℝ)) * b p.1 p.2 := by
  refine Finset.sum_subset (Finset.offDiag_mono (Finset.union_subset hA hB)) ?_
  rintro ⟨x, y⟩ hxy hnot
  rcases Finset.mem_offDiag.mp hxy with ⟨_, _, hne⟩
  by_cases hxA : x ∈ A.support
  · by_cases hyB : y ∈ B.support
    · exact absurd (Finset.mem_offDiag.mpr
        ⟨Finset.mem_union_left _ hxA, Finset.mem_union_right _ hyB, hne⟩) hnot
    · simp [Finsupp.notMem_support_iff.mp hyB]
  · simp [Finsupp.notMem_support_iff.mp hxA]

private theorem pairDiag_ext {X : Type} [DecidableEq X] (t : X → ℝ) (A B : X →₀ ℤ)
    {U : Finset X} (hA : A.support ⊆ U) (hB : B.support ⊆ U) :
    pairDiag t A B = ∑ v ∈ U, ((A v : ℝ) * (B v : ℝ)) * t v := by
  refine Finset.sum_subset (Finset.union_subset hA hB) ?_
  intro x _ hnot
  by_cases hxA : x ∈ A.support
  · have hxB : x ∉ B.support := fun h => hnot (Finset.mem_union_right _ h)
    simp [Finsupp.notMem_support_iff.mp hxB]
  · simp [Finsupp.notMem_support_iff.mp hxA]

private theorem pairOff_self {X : Type} [DecidableEq X] (b : X → X → ℝ) (A : X →₀ ℤ) :
    pairOff b A A = ∑ p ∈ A.support.offDiag, ((A p.1 : ℝ) * (A p.2 : ℝ)) * b p.1 p.2 := by
  simp [pairOff]

private theorem auxAbs_over {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ)
    (A : X →₀ ℤ) {U : Finset X} (hA : A.support ⊆ U) :
    auxAbs γ t b A
      = ((γ : ℝ) + (∑ v ∈ U, (A v : ℝ)) - 1) * (∑ v ∈ U, (A v : ℝ) * t v)
        - (∑ p ∈ U.offDiag, ((A p.1 : ℝ) * (A p.2 : ℝ)) * b p.1 p.2) / 2
        - (2 - 2 * (γ : ℝ)) * (∑ v ∈ U, ((A v : ℝ) * ((A v : ℝ) - 1) / 2) * t v) := by
  rw [auxAbs, sum_ext_deg A hA, sum_ext_weight A t hA, sum_ext_selfpair A t hA,
    ← pairOff_self b A, pairOff_ext b A A hA hA]

private theorem sum_offDiag_eq_double {X : Type} [DecidableEq X] (U : Finset X)
    (F : X → X → ℝ) :
    ∑ p ∈ U.offDiag, F p.1 p.2 = ∑ v ∈ U, ∑ w ∈ U.erase v, F v w := by
  have hU : U.offDiag = U.biUnion fun v => {v} ×ˢ U.erase v := by
    ext ⟨x, y⟩
    simp only [Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨x, hx, rfl, Ne.symm hxy, hy⟩
    · rintro ⟨v, hv, rfl, hyx, hy⟩
      exact ⟨hv, hy, Ne.symm hyx⟩
  rw [hU, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_product]
    simp
  · intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton]
    rintro ⟨x, y⟩ ⟨hx1, -⟩ ⟨hx2, -⟩
    exact hab (hx1.symm.trans hx2)

private theorem pairOff_comm {X : Type} [DecidableEq X] (b : X → X → ℝ)
    (hsym : ∀ v w, b v w = b w v) (A B : X →₀ ℤ) :
    pairOff b A B = pairOff b B A := by
  classical
  have himg : (A.support ∪ B.support).offDiag.image Prod.swap
      = (A.support ∪ B.support).offDiag := by
    ext ⟨x, y⟩
    simp only [Finset.mem_image, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨a1, a2⟩, ⟨ha1, ha2, hne⟩, hswap⟩
      rw [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
      obtain ⟨rfl, rfl⟩ := hswap
      exact ⟨ha2, ha1, Ne.symm hne⟩
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨(y, x), ⟨hy, hx, Ne.symm hxy⟩, rfl⟩
  rw [pairOff_ext b A B Finset.subset_union_left Finset.subset_union_right,
    pairOff_ext b B A (U := A.support ∪ B.support) Finset.subset_union_right
      Finset.subset_union_left]
  calc ∑ p ∈ (A.support ∪ B.support).offDiag, ((A p.1 : ℝ) * (B p.2 : ℝ)) * b p.1 p.2
      = ∑ p ∈ (A.support ∪ B.support).offDiag.image Prod.swap,
          ((A p.1 : ℝ) * (B p.2 : ℝ)) * b p.1 p.2 := by rw [himg]
    _ = ∑ p ∈ (A.support ∪ B.support).offDiag,
          ((A p.2 : ℝ) * (B p.1 : ℝ)) * b p.2 p.1 := by
        rw [Finset.sum_image (fun _ _ _ _ h => Prod.swap_injective h)]
        exact Finset.sum_congr rfl fun x _ => rfl
    _ = ∑ p ∈ (A.support ∪ B.support).offDiag, ((B p.1 : ℝ) * (A p.2 : ℝ)) * b p.1 p.2 := by
        exact Finset.sum_congr rfl fun p _ => by rw [hsym p.2 p.1]; ring

private theorem sum_erase_term {X : Type} [DecidableEq X] (Q : X →₀ ℤ) (g : X → ℝ) (v : X) :
    ∑ w ∈ Q.support.erase v, (Q w : ℝ) * g w
      = (∑ w ∈ Q.support, (Q w : ℝ) * g w) - (Q v : ℝ) * g v := by
  by_cases hv : v ∈ Q.support
  · have h := Finset.add_sum_erase Q.support (fun w => (Q w : ℝ) * g w) hv
    linarith
  · rw [Finset.erase_eq_self.mpr hv, Finsupp.notMem_support_iff.mp hv]
    simp

private theorem pairOff_eq_double {X : Type} [DecidableEq X] (b : X → X → ℝ) (A Q : X →₀ ℤ) :
    (∑ v ∈ A.support, (A v : ℝ) * ∑ w ∈ Q.support.erase v, (Q w : ℝ) * b v w)
      = pairOff b A Q := by
  classical
  have hinner : ∀ v : X, (∑ w ∈ Q.support.erase v, (Q w : ℝ) * b v w)
      = ∑ w ∈ (A.support ∪ Q.support).erase v, (Q w : ℝ) * b v w := by
    intro v
    refine Finset.sum_subset (Finset.erase_subset_erase _ Finset.subset_union_right) ?_
    intro w hw hnw
    rcases Finset.mem_erase.mp hw with ⟨hne, _⟩
    have hq : Q w = 0 := by
      by_contra h
      exact hnw (Finset.mem_erase.mpr ⟨hne, Finsupp.mem_support_iff.mpr h⟩)
    simp [hq]
  calc (∑ v ∈ A.support, (A v : ℝ) * ∑ w ∈ Q.support.erase v, (Q w : ℝ) * b v w)
      = ∑ v ∈ A.support ∪ Q.support,
          (A v : ℝ) * ∑ w ∈ Q.support.erase v, (Q w : ℝ) * b v w := by
        refine Finset.sum_subset Finset.subset_union_left fun v _ hnv => ?_
        simp [Finsupp.notMem_support_iff.mp hnv]
    _ = ∑ v ∈ A.support ∪ Q.support, ∑ w ∈ (A.support ∪ Q.support).erase v,
          (A v : ℝ) * ((Q w : ℝ) * b v w) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hinner v, Finset.mul_sum]
    _ = ∑ p ∈ (A.support ∪ Q.support).offDiag,
          (A p.1 : ℝ) * ((Q p.2 : ℝ) * b p.1 p.2) :=
        (sum_offDiag_eq_double _ _).symm
    _ = pairOff b A Q := by
        rw [pairOff_ext b A Q Finset.subset_union_left Finset.subset_union_right]
        exact Finset.sum_congr rfl fun p _ => by ring

private theorem pairDiag_eq_single {X : Type} [DecidableEq X] (t : X → ℝ) (A Q : X →₀ ℤ) :
    pairDiag t A Q = ∑ v ∈ A.support, ((A v : ℝ) * (Q v : ℝ)) * t v :=
  (Finset.sum_subset Finset.subset_union_left fun v _ hnv => by
    simp [Finsupp.notMem_support_iff.mp hnv]).symm

private theorem auxAbs_add {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ)
    (D E : X →₀ ℤ) :
    auxAbs γ t b (D + E)
      = auxAbs γ t b D
        + (E.sum fun _ n => (n : ℝ)) * (D.sum fun v n => (n : ℝ) * t v)
        + ((γ : ℝ) + (D.sum fun _ n => (n : ℝ)) + (E.sum fun _ n => (n : ℝ)) - 1)
            * (E.sum fun v n => (n : ℝ) * t v)
        - (pairOff b D E + pairOff b E D + pairOff b E E) / 2
        - (2 - 2 * (γ : ℝ))
            * (pairDiag t D E + E.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * t v) := by
  classical
  have hDU : D.support ⊆ D.support ∪ E.support := Finset.subset_union_left
  have hEU : E.support ⊆ D.support ∪ E.support := Finset.subset_union_right
  have hDEU : (D + E).support ⊆ D.support ∪ E.support := Finsupp.support_add
  rw [auxAbs_over γ t b (D + E) hDEU, auxAbs_over γ t b D hDU,
    sum_ext_deg D hDU, sum_ext_deg E hEU, sum_ext_weight D t hDU, sum_ext_weight E t hEU,
    sum_ext_selfpair E t hEU,
    pairOff_ext b D E hDU hEU, pairOff_ext b E D hEU hDU, pairOff_ext b E E hEU hEU,
    pairDiag_ext t D E hDU hEU]
  simp only [Finsupp.add_apply, Int.cast_add]
  have hdeg : ∑ v ∈ D.support ∪ E.support, ((D v : ℝ) + (E v : ℝ))
      = (∑ v ∈ D.support ∪ E.support, (D v : ℝ))
        + ∑ v ∈ D.support ∪ E.support, (E v : ℝ) :=
    Finset.sum_add_distrib
  have hT : ∑ v ∈ D.support ∪ E.support, ((D v : ℝ) + (E v : ℝ)) * t v
      = (∑ v ∈ D.support ∪ E.support, (D v : ℝ) * t v)
        + ∑ v ∈ D.support ∪ E.support, (E v : ℝ) * t v := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hB : ∑ p ∈ (D.support ∪ E.support).offDiag,
        (((D p.1 : ℝ) + (E p.1 : ℝ)) * ((D p.2 : ℝ) + (E p.2 : ℝ))) * b p.1 p.2
      = (∑ p ∈ (D.support ∪ E.support).offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * b p.1 p.2)
        + ((∑ p ∈ (D.support ∪ E.support).offDiag, ((D p.1 : ℝ) * (E p.2 : ℝ)) * b p.1 p.2)
        + ((∑ p ∈ (D.support ∪ E.support).offDiag, ((E p.1 : ℝ) * (D p.2 : ℝ)) * b p.1 p.2)
        + ∑ p ∈ (D.support ∪ E.support).offDiag, ((E p.1 : ℝ) * (E p.2 : ℝ)) * b p.1 p.2)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hS : ∑ v ∈ D.support ∪ E.support,
        (((D v : ℝ) + (E v : ℝ)) * (((D v : ℝ) + (E v : ℝ)) - 1) / 2) * t v
      = (∑ v ∈ D.support ∪ E.support, ((D v : ℝ) * ((D v : ℝ) - 1) / 2) * t v)
        + ((∑ v ∈ D.support ∪ E.support, ((D v : ℝ) * (E v : ℝ)) * t v)
        + ∑ v ∈ D.support ∪ E.support, ((E v : ℝ) * ((E v : ℝ) - 1) / 2) * t v) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hdeg, hT, hB, hS]
  ring

private theorem phiC_eq {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ)
    (Q : X →₀ ℤ) (c : ℤ) (A : X →₀ ℤ) :
    phiC γ t b Q c A
      = (A.sum fun _ n => (n : ℝ)) * (Q.sum fun v n => (n : ℝ) * t v)
        + (2 * (γ : ℝ) - 2) * pairDiag t A Q - pairOff b A Q
        - (c : ℝ) * (A.sum fun v n => (n : ℝ) * t v) := by
  classical
  have hexp : phiC γ t b Q c A
      = (∑ v ∈ A.support, (A v : ℝ) * ∑ w ∈ Q.support, (Q w : ℝ) * t w)
        - (∑ v ∈ A.support, ((A v : ℝ) * (Q v : ℝ)) * t v)
        - (∑ v ∈ A.support, (A v : ℝ) * ∑ w ∈ Q.support.erase v, (Q w : ℝ) * b v w)
        + (2 * (γ : ℝ) - 1) * (∑ v ∈ A.support, ((A v : ℝ) * (Q v : ℝ)) * t v)
        - (c : ℝ) * (∑ v ∈ A.support, (A v : ℝ) * t v) := by
    unfold phiC ePt
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hsplit : (∑ w ∈ Q.support.erase v, (Q w : ℝ) * (t w - b v w))
        = (∑ w ∈ Q.support.erase v, (Q w : ℝ) * t w)
          - ∑ w ∈ Q.support.erase v, (Q w : ℝ) * b v w := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hsplit, sum_erase_term Q t v]
    ring
  rw [hexp, pairOff_eq_double b A Q, pairDiag_eq_single t A Q, ← Finset.sum_mul,
    sum_ext_deg A (le_refl A.support), sum_ext_weight A t (le_refl A.support),
    sum_ext_weight Q t (le_refl Q.support)]
  ring

private theorem selfpair_bridge {X : Type} [DecidableEq X] (t : X → ℝ) (Q : X →₀ ℤ) :
    (Q.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * t v)
      = (1 / 2) * pairDiag t Q Q - (1 / 2) * (Q.sum fun v n => (n : ℝ) * t v) := by
  classical
  rw [pairDiag_eq_single t Q Q, sum_ext_selfpair Q t (le_refl Q.support),
    sum_ext_weight Q t (le_refl Q.support), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

private theorem regroup {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ)
    (hsym : ∀ v w, b v w = b w v) (A Q : X →₀ ℤ) (c : ℤ) :
    auxAbs γ t b (A + Q)
      = auxAbs γ t b A + phiC γ t b Q c A + (1 / 2) * phiC γ t b Q c Q
        + ((Q.sum fun _ n => (n : ℝ)) + (c : ℝ))
            * ((A.sum fun v n => (n : ℝ) * t v)
              + (1 / 2) * (Q.sum fun v n => (n : ℝ) * t v)) := by
  classical
  rw [auxAbs_add γ t b A Q, phiC_eq γ t b Q c A, phiC_eq γ t b Q c Q,
    pairOff_comm b hsym Q A, selfpair_bridge t Q]
  ring
private theorem sum_erase_deg {X : Type} [DecidableEq X] (Q : X →₀ ℤ) (v : X) :
    ∑ w ∈ Q.support.erase v, (Q w : ℝ) = (∑ w ∈ Q.support, (Q w : ℝ)) - (Q v : ℝ) := by
  by_cases hv : v ∈ Q.support
  · have h := Finset.add_sum_erase Q.support (fun w => (Q w : ℝ)) hv
    linarith
  · rw [Finset.erase_eq_self.mpr hv, Finsupp.notMem_support_iff.mp hv]
    simp

end B0R1

namespace B0Arith

open B0R1 Finset

variable {X : Type} [DecidableEq X]

private theorem abs_phiC_le (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ) (Q : X →₀ ℤ) (c : ℤ) (A : X →₀ ℤ) :
    |phiC γ t b Q c A| ≤ ∑ v ∈ A.support, |(A v : ℝ)| * |ePt γ t b Q c v| :=
  (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun _ _ => abs_mul _ _)

private theorem apply_le_of_sum {E : X →₀ ℤ} (hE : ∀ w, 0 ≤ E w) {n : ℤ}
    (hsum : (E.sum fun _ m => m) = n) (v : X) : E v ≤ n := by
  by_cases hv : v ∈ E.support
  · calc E v ≤ ∑ w ∈ E.support, E w := Finset.single_le_sum (fun w _ => hE w) hv
      _ = n := hsum
  · rw [Finsupp.notMem_support_iff.mp hv]
    calc (0 : ℤ) ≤ E v := hE v
      _ ≤ n := by
        by_cases hv' : v ∈ E.support
        · exact absurd hv' hv
        · rw [Finsupp.notMem_support_iff.mp hv]
          calc (0 : ℤ) = ∑ w ∈ E.support, 0 := by simp
            _ ≤ ∑ w ∈ E.support, E w := Finset.sum_le_sum fun w _ => hE w
            _ = n := hsum

private theorem wsum_le (o : X) {pt : X → ℝ} (hpt : ∀ v, 0 ≤ pt v) {E : X →₀ ℤ}
    (hE : ∀ w, 0 ≤ E w) (W : Finset X) :
    ∑ v ∈ W, ((E.erase o) v : ℝ) * pt v ≤ (E.erase o).sum fun v m => (m : ℝ) * pt v := by
  have hterm : ∀ v, 0 ≤ ((E.erase o) v : ℝ) * pt v := by
    intro v
    refine mul_nonneg ?_ (hpt v)
    by_cases hv : v = o
    · subst hv; rw [Finsupp.erase_same]; simp
    · rw [Finsupp.erase_ne hv]
      exact_mod_cast hE v
  calc ∑ v ∈ W, ((E.erase o) v : ℝ) * pt v
      ≤ ∑ v ∈ W ∪ (E.erase o).support, ((E.erase o) v : ℝ) * pt v :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun v _ _ => hterm v)
    _ = ∑ v ∈ (E.erase o).support, ((E.erase o) v : ℝ) * pt v :=
        (Finset.sum_subset Finset.subset_union_right (fun v _ hv => by
          rw [Finsupp.notMem_support_iff.mp hv]; simp)).symm
    _ = (E.erase o).sum fun v m => (m : ℝ) * pt v := by
        simp only [Finsupp.sum]

private theorem _root_.B0Arith.subrow_ARITH (o : X) (γ : ℤ) (t : X → ℝ)
    (b : X → X → ℝ) (pt : X → ℝ) (D₁ D₂ : X →₀ ℤ) (n : ℕ)
    (heff₁ : ∀ w, 0 ≤ D₁ w) (heff₂ : ∀ w, 0 ≤ D₂ w)
    (hsum₁ : (D₁.sum fun _ m => m) = (n : ℤ)) (hsum₂ : (D₂.sum fun _ m => m) = (n : ℤ))
    (hpt : ∀ v, 0 ≤ pt v)
    (ε c B C₁ h₁ h₂ : ℝ) (hε : 0 < ε) (hεn : ε * ((n : ℝ) + 1) ≤ 1) (hB0 : 0 ≤ B)
    (hR4 : ∀ v, v ≠ o →
      |ePt γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) v|
        ≤ ε * |((D₁ - D₂) v : ℝ)| * pt v + c * ((D₁ - D₂).sum fun _ m => |(m : ℝ)|))
    (hS₁ : ((D₁.erase o).sum fun v m => (m : ℝ) * pt v) ≤ B * h₁ + C₁)
    (hS₂ : ((D₂.erase o).sum fun v m => (m : ℝ) * pt v) ≤ B * h₂ + C₁) :
    phiC γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) (D₂.erase o)
      + (1 / 2) * phiC γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) ((D₁ - D₂).erase o)
      ≤ 2 * B * (h₁ + h₂) + (4 * C₁ + 4 * (n : ℝ) ^ 2 * |c|) := by
  classical
  have _ := hB0

  set P : X →₀ ℤ := D₁ - D₂ with hPdef

  set mass : ℝ := P.sum fun _ m => |(m : ℝ)| with hmass
  have hmass0 : 0 ≤ mass := by
    rw [hmass, Finsupp.sum]
    exact Finset.sum_nonneg fun v _ => abs_nonneg _
  have hPabs : ∀ v, |(P v : ℝ)| ≤ ((D₁ v : ℝ) + (D₂ v : ℝ)) := by
    intro v
    rw [hPdef, Finsupp.sub_apply]
    push_cast
    calc |(D₁ v : ℝ) - (D₂ v : ℝ)| ≤ |(D₁ v : ℝ)| + |(D₂ v : ℝ)| := abs_sub _ _
      _ = (D₁ v : ℝ) + (D₂ v : ℝ) := by
          rw [abs_of_nonneg (by exact_mod_cast heff₁ v),
            abs_of_nonneg (by exact_mod_cast heff₂ v)]
  have hD₁n : ∀ v, (D₁ v : ℝ) ≤ (n : ℝ) := fun v => by
    exact_mod_cast apply_le_of_sum heff₁ hsum₁ v
  have hD₂n : ∀ v, (D₂ v : ℝ) ≤ (n : ℝ) := fun v => by
    exact_mod_cast apply_le_of_sum heff₂ hsum₂ v
  have hPsupp : P.support ⊆ D₁.support ∪ D₂.support := by
    intro v hv
    rw [Finset.mem_union]
    by_contra hcon
    push Not at hcon
    exact (Finsupp.mem_support_iff.mp hv) (by
      rw [hPdef, Finsupp.sub_apply, Finsupp.notMem_support_iff.mp hcon.1,
        Finsupp.notMem_support_iff.mp hcon.2, sub_zero])
  have hmass2n : mass ≤ 2 * (n : ℝ) := by
    rw [hmass, Finsupp.sum]
    calc ∑ v ∈ P.support, |(P v : ℝ)|
        ≤ ∑ v ∈ P.support, ((D₁ v : ℝ) + (D₂ v : ℝ)) :=
          Finset.sum_le_sum fun v _ => hPabs v
      _ ≤ ∑ v ∈ D₁.support ∪ D₂.support, ((D₁ v : ℝ) + (D₂ v : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsupp (fun v _ _ =>
            add_nonneg (by exact_mod_cast heff₁ v) (by exact_mod_cast heff₂ v))
      _ = (∑ v ∈ D₁.support ∪ D₂.support, (D₁ v : ℝ))
          + ∑ v ∈ D₁.support ∪ D₂.support, (D₂ v : ℝ) := Finset.sum_add_distrib
      _ ≤ (n : ℝ) + (n : ℝ) := by
          have e₁ : ∑ v ∈ D₁.support ∪ D₂.support, (D₁ v : ℝ) = (n : ℝ) := by
            rw [← (Finset.sum_subset Finset.subset_union_left (fun v _ hv => by
              rw [Finsupp.notMem_support_iff.mp hv]; simp))]
            have h2 : (∑ v ∈ D₁.support, D₁ v) = (n : ℤ) := hsum₁
            exact_mod_cast h2
          have e₂ : ∑ v ∈ D₁.support ∪ D₂.support, (D₂ v : ℝ) = (n : ℝ) := by
            rw [← (Finset.sum_subset Finset.subset_union_right (fun v _ hv => by
              rw [Finsupp.notMem_support_iff.mp hv]; simp))]
            have h2 : (∑ v ∈ D₂.support, D₂ v) = (n : ℤ) := hsum₂
            exact_mod_cast h2
          rw [e₁, e₂]
      _ = 2 * (n : ℝ) := by ring

  have hcm : c * mass ≤ |c| * mass :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hmass0

  have hA₂mem : ∀ v ∈ (D₂.erase o).support, v ≠ o := by
    intro v hv
    rw [Finsupp.support_erase] at hv
    exact (Finset.mem_erase.mp hv).1
  have hA₂val : ∀ v ∈ (D₂.erase o).support, ((D₂.erase o) v : ℝ) = (D₂ v : ℝ) := by
    intro v hv
    rw [Finsupp.erase_ne (hA₂mem v hv)]
  have hQmem : ∀ v ∈ (P.erase o).support, v ≠ o := by
    intro v hv
    rw [Finsupp.support_erase] at hv
    exact (Finset.mem_erase.mp hv).1
  have hQval : ∀ v ∈ (P.erase o).support, ((P.erase o) v : ℝ) = (P v : ℝ) := by
    intro v hv
    rw [Finsupp.erase_ne (hQmem v hv)]

  have hŜnonneg : ∀ (E : X →₀ ℤ), (∀ w, 0 ≤ E w) →
      0 ≤ (E.erase o).sum fun v m => (m : ℝ) * pt v := by
    intro E hE
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun v hv => mul_nonneg ?_ (hpt v)
    rw [Finsupp.erase_ne ?_]
    · exact_mod_cast hE v
    · rw [Finsupp.support_erase] at hv
      exact (Finset.mem_erase.mp hv).1

  have hsumD₁A₂ : ∑ v ∈ (D₂.erase o).support, (D₁ v : ℝ) * pt v
      ≤ (D₁.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (D₂.erase o).support, (D₁ v : ℝ) * pt v
        = ∑ v ∈ (D₂.erase o).support, ((D₁.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hA₂mem v hv)]
      _ ≤ _ := wsum_le o hpt heff₁ _
  have hsumD₂A₂ : ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * pt v
      ≤ (D₂.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * pt v
        = ∑ v ∈ (D₂.erase o).support, ((D₂.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hA₂mem v hv)]
      _ ≤ _ := wsum_le o hpt heff₂ _
  have hsumD₁Q : ∑ v ∈ (P.erase o).support, (D₁ v : ℝ) * pt v
      ≤ (D₁.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (P.erase o).support, (D₁ v : ℝ) * pt v
        = ∑ v ∈ (P.erase o).support, ((D₁.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hQmem v hv)]
      _ ≤ _ := wsum_le o hpt heff₁ _
  have hsumD₂Q : ∑ v ∈ (P.erase o).support, (D₂ v : ℝ) * pt v
      ≤ (D₂.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (P.erase o).support, (D₂ v : ℝ) * pt v
        = ∑ v ∈ (P.erase o).support, ((D₂.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hQmem v hv)]
      _ ≤ _ := wsum_le o hpt heff₂ _
  set Ŝ₁ : ℝ := (D₁.erase o).sum fun v m => (m : ℝ) * pt v with hŜ₁def
  set Ŝ₂ : ℝ := (D₂.erase o).sum fun v m => (m : ℝ) * pt v with hŜ₂def
  have hŜ₁0 : 0 ≤ Ŝ₁ := hŜnonneg D₁ heff₁
  have hŜ₂0 : 0 ≤ Ŝ₂ := hŜnonneg D₂ heff₂

  have hbranchA : |phiC γ t b (P.erase o) (P o) (D₂.erase o)|
      ≤ ε * ((n : ℝ) * (Ŝ₁ + Ŝ₂)) + (n : ℝ) * (|c| * mass) := by
    calc |phiC γ t b (P.erase o) (P o) (D₂.erase o)|
        ≤ ∑ v ∈ (D₂.erase o).support,
            |((D₂.erase o) v : ℝ)| * |ePt γ t b (P.erase o) (P o) v| :=
          abs_phiC_le γ t b (P.erase o) (P o) (D₂.erase o)
      _ ≤ ∑ v ∈ (D₂.erase o).support,
            (D₂ v : ℝ) * (ε * |(P v : ℝ)| * pt v + c * mass) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hA₂val v hv, abs_of_nonneg (by exact_mod_cast heff₂ v : (0:ℝ) ≤ (D₂ v : ℝ))]
          exact mul_le_mul_of_nonneg_left (hR4 v (hA₂mem v hv))
            (by exact_mod_cast heff₂ v)
      _ = ε * (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * (|(P v : ℝ)| * pt v))
          + (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (c * mass) := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ ε * ((n : ℝ) * (Ŝ₁ + Ŝ₂)) + (n : ℝ) * (|c| * mass) := by
          have h1 : ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * (|(P v : ℝ)| * pt v)
              ≤ (n : ℝ) * (Ŝ₁ + Ŝ₂) := by
            calc ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * (|(P v : ℝ)| * pt v)
                ≤ ∑ v ∈ (D₂.erase o).support,
                    (n : ℝ) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                  refine Finset.sum_le_sum fun v hv => ?_
                  have hD₂0 : (0:ℝ) ≤ (D₂ v : ℝ) := by exact_mod_cast heff₂ v
                  calc (D₂ v : ℝ) * (|(P v : ℝ)| * pt v)
                      ≤ (n : ℝ) * (|(P v : ℝ)| * pt v) :=
                        mul_le_mul_of_nonneg_right (hD₂n v)
                          (mul_nonneg (abs_nonneg _) (hpt v))
                    _ ≤ (n : ℝ) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
                        exact mul_le_mul_of_nonneg_right (hPabs v) (hpt v)
              _ = (n : ℝ) * ((∑ v ∈ (D₂.erase o).support, (D₁ v : ℝ) * pt v)
                  + ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * pt v) := by
                  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun v _ => by ring
              _ ≤ (n : ℝ) * (Ŝ₁ + Ŝ₂) := by
                  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
                  exact add_le_add hsumD₁A₂ hsumD₂A₂
          have h2 : (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (c * mass)
              ≤ (n : ℝ) * (|c| * mass) := by
            have hw0 : 0 ≤ ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) :=
              Finset.sum_nonneg fun v _ => by exact_mod_cast heff₂ v
            have hwn : ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) ≤ (n : ℝ) := by
              calc ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)
                  ≤ ∑ v ∈ D₂.support, (D₂ v : ℝ) := by
                    rw [Finsupp.support_erase]
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.erase_subset o D₂.support)
                      (fun v _ _ => by exact_mod_cast heff₂ v)
                _ = (n : ℝ) := by
                    have h2 : (∑ v ∈ D₂.support, D₂ v) = (n : ℤ) := hsum₂
                    exact_mod_cast h2
            calc (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (c * mass)
                ≤ (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_left hcm hw0
              _ ≤ (n : ℝ) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_right hwn (mul_nonneg (abs_nonneg _) hmass0)
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (le_of_lt hε)) h2

  have hbranchQ : |phiC γ t b (P.erase o) (P o) (P.erase o)|
      ≤ ε * ((2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂)) + (2 * (n : ℝ)) * (|c| * mass) := by
    calc |phiC γ t b (P.erase o) (P o) (P.erase o)|
        ≤ ∑ v ∈ (P.erase o).support,
            |((P.erase o) v : ℝ)| * |ePt γ t b (P.erase o) (P o) v| :=
          abs_phiC_le γ t b (P.erase o) (P o) (P.erase o)
      _ ≤ ∑ v ∈ (P.erase o).support,
            |(P v : ℝ)| * (ε * |(P v : ℝ)| * pt v + c * mass) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hQval v hv]
          exact mul_le_mul_of_nonneg_left (hR4 v (hQmem v hv)) (abs_nonneg _)
      _ = ε * (∑ v ∈ (P.erase o).support, |(P v : ℝ)| * (|(P v : ℝ)| * pt v))
          + (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (c * mass) := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ ε * ((2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂)) + (2 * (n : ℝ)) * (|c| * mass) := by
          have h1 : ∑ v ∈ (P.erase o).support, |(P v : ℝ)| * (|(P v : ℝ)| * pt v)
              ≤ (2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂) := by
            calc ∑ v ∈ (P.erase o).support, |(P v : ℝ)| * (|(P v : ℝ)| * pt v)
                ≤ ∑ v ∈ (P.erase o).support,
                    (2 * (n : ℝ)) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                  refine Finset.sum_le_sum fun v hv => ?_
                  have hP2n : |(P v : ℝ)| ≤ 2 * (n : ℝ) :=
                    (hPabs v).trans (by linarith [hD₁n v, hD₂n v])
                  calc |(P v : ℝ)| * (|(P v : ℝ)| * pt v)
                      ≤ (2 * (n : ℝ)) * (|(P v : ℝ)| * pt v) :=
                        mul_le_mul_of_nonneg_right hP2n
                          (mul_nonneg (abs_nonneg _) (hpt v))
                    _ ≤ (2 * (n : ℝ)) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                        exact mul_le_mul_of_nonneg_right (hPabs v) (hpt v)
              _ = (2 * (n : ℝ)) * ((∑ v ∈ (P.erase o).support, (D₁ v : ℝ) * pt v)
                  + ∑ v ∈ (P.erase o).support, (D₂ v : ℝ) * pt v) := by
                  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun v _ => by ring
              _ ≤ (2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact add_le_add hsumD₁Q hsumD₂Q
          have h2 : (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (c * mass)
              ≤ (2 * (n : ℝ)) * (|c| * mass) := by
            have hw0 : 0 ≤ ∑ v ∈ (P.erase o).support, |(P v : ℝ)| :=
              Finset.sum_nonneg fun v _ => abs_nonneg _
            have hwm : ∑ v ∈ (P.erase o).support, |(P v : ℝ)| ≤ mass := by
              rw [hmass, Finsupp.sum]
              calc ∑ v ∈ (P.erase o).support, |(P v : ℝ)|
                  ≤ ∑ v ∈ P.support, |(P v : ℝ)| := by
                    rw [Finsupp.support_erase]
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.erase_subset o P.support) (fun v _ _ => abs_nonneg _)
                _ = ∑ v ∈ P.support, |(P v : ℝ)| := rfl
            calc (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (c * mass)
                ≤ (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_left hcm hw0
              _ ≤ mass * (|c| * mass) :=
                  mul_le_mul_of_nonneg_right hwm (mul_nonneg (abs_nonneg _) hmass0)
              _ ≤ (2 * (n : ℝ)) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_right hmass2n
                    (mul_nonneg (abs_nonneg _) hmass0)
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (le_of_lt hε)) h2

  have hεn' : ε * (n : ℝ) ≤ 1 := by
    have : ε * (n : ℝ) ≤ ε * ((n : ℝ) + 1) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hε)
    linarith
  have hŜsum : Ŝ₁ + Ŝ₂ ≤ (B * h₁ + C₁) + (B * h₂ + C₁) := add_le_add hS₁ hS₂
  have hεpart : 2 * (ε * (n : ℝ)) * (Ŝ₁ + Ŝ₂) ≤ 2 * (Ŝ₁ + Ŝ₂) := by
    have h0 : 0 ≤ Ŝ₁ + Ŝ₂ := add_nonneg hŜ₁0 hŜ₂0
    nlinarith [hεn', h0]
  have hmasscm : |c| * mass ≤ |c| * (2 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hmass2n (abs_nonneg c)
  calc phiC γ t b (P.erase o) (P o) (D₂.erase o)
      + (1 / 2) * phiC γ t b (P.erase o) (P o) (P.erase o)
      ≤ |phiC γ t b (P.erase o) (P o) (D₂.erase o)|
        + (1 / 2) * |phiC γ t b (P.erase o) (P o) (P.erase o)| := by
        have := le_abs_self (phiC γ t b (P.erase o) (P o) (D₂.erase o))
        have := le_abs_self (phiC γ t b (P.erase o) (P o) (P.erase o))
        linarith
    _ ≤ (ε * ((n : ℝ) * (Ŝ₁ + Ŝ₂)) + (n : ℝ) * (|c| * mass))
        + (1 / 2) * (ε * ((2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂)) + (2 * (n : ℝ)) * (|c| * mass)) := by
        have h2 : (0:ℝ) ≤ 1 / 2 := by norm_num
        linarith [hbranchA, mul_le_mul_of_nonneg_left hbranchQ h2]
    _ = 2 * (ε * (n : ℝ)) * (Ŝ₁ + Ŝ₂) + 2 * (n : ℝ) * (|c| * mass) := by ring
    _ ≤ 2 * (Ŝ₁ + Ŝ₂) + 2 * (n : ℝ) * (|c| * (2 * (n : ℝ))) := by
        have hn0 : (0:ℝ) ≤ 2 * (n : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hmasscm hn0
        linarith [hεpart]
    _ ≤ 2 * ((B * h₁ + C₁) + (B * h₂ + C₁)) + 2 * (n : ℝ) * (|c| * (2 * (n : ℝ))) := by
        linarith [hŜsum]
    _ = 2 * B * (h₁ + h₂) + (4 * C₁ + 4 * (n : ℝ) ^ 2 * |c|) := by ring

p2m_export "B0Arith" "subrow_ARITH"

private theorem subrow_ARITH_eps {X : Type} [DecidableEq X] (o : X) (γ : ℤ) (t : X → ℝ)
    (b : X → X → ℝ) (pt : X → ℝ) (D₁ D₂ : X →₀ ℤ) (n : ℕ)
    (heff₁ : ∀ w, 0 ≤ D₁ w) (heff₂ : ∀ w, 0 ≤ D₂ w)
    (hsum₁ : (D₁.sum fun _ m => m) = (n : ℤ)) (hsum₂ : (D₂.sum fun _ m => m) = (n : ℤ))
    (hpt : ∀ v, 0 ≤ pt v)
    (ε c B C₁ h₁ h₂ ε₀ : ℝ) (hε : 0 < ε) (hε₀ : 0 < ε₀)
    (hεn : ε * ((n : ℝ) + 1) ≤ ε₀) (hB0 : 0 ≤ B)
    (hR4 : ∀ v, v ≠ o →
      |ePt γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) v|
        ≤ ε * |((D₁ - D₂) v : ℝ)| * pt v + c * ((D₁ - D₂).sum fun _ m => |(m : ℝ)|))
    (hS₁ : ((D₁.erase o).sum fun v m => (m : ℝ) * pt v) ≤ B * h₁ + C₁)
    (hS₂ : ((D₂.erase o).sum fun v m => (m : ℝ) * pt v) ≤ B * h₂ + C₁) :
    phiC γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) (D₂.erase o)
      + (1 / 2) * phiC γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) ((D₁ - D₂).erase o)
      ≤ 2 * ε₀ * B * (h₁ + h₂) + (4 * ε₀ * C₁ + 4 * (n : ℝ) ^ 2 * |c|) := by
  classical
  have _ := hB0

  set P : X →₀ ℤ := D₁ - D₂ with hPdef

  set mass : ℝ := P.sum fun _ m => |(m : ℝ)| with hmass
  have hmass0 : 0 ≤ mass := by
    rw [hmass, Finsupp.sum]
    exact Finset.sum_nonneg fun v _ => abs_nonneg _
  have hPabs : ∀ v, |(P v : ℝ)| ≤ ((D₁ v : ℝ) + (D₂ v : ℝ)) := by
    intro v
    rw [hPdef, Finsupp.sub_apply]
    push_cast
    calc |(D₁ v : ℝ) - (D₂ v : ℝ)| ≤ |(D₁ v : ℝ)| + |(D₂ v : ℝ)| := abs_sub _ _
      _ = (D₁ v : ℝ) + (D₂ v : ℝ) := by
          rw [abs_of_nonneg (by exact_mod_cast heff₁ v),
            abs_of_nonneg (by exact_mod_cast heff₂ v)]
  have hD₁n : ∀ v, (D₁ v : ℝ) ≤ (n : ℝ) := fun v => by
    exact_mod_cast apply_le_of_sum heff₁ hsum₁ v
  have hD₂n : ∀ v, (D₂ v : ℝ) ≤ (n : ℝ) := fun v => by
    exact_mod_cast apply_le_of_sum heff₂ hsum₂ v
  have hPsupp : P.support ⊆ D₁.support ∪ D₂.support := by
    intro v hv
    rw [Finset.mem_union]
    by_contra hcon
    push Not at hcon
    exact (Finsupp.mem_support_iff.mp hv) (by
      rw [hPdef, Finsupp.sub_apply, Finsupp.notMem_support_iff.mp hcon.1,
        Finsupp.notMem_support_iff.mp hcon.2, sub_zero])
  have hmass2n : mass ≤ 2 * (n : ℝ) := by
    rw [hmass, Finsupp.sum]
    calc ∑ v ∈ P.support, |(P v : ℝ)|
        ≤ ∑ v ∈ P.support, ((D₁ v : ℝ) + (D₂ v : ℝ)) :=
          Finset.sum_le_sum fun v _ => hPabs v
      _ ≤ ∑ v ∈ D₁.support ∪ D₂.support, ((D₁ v : ℝ) + (D₂ v : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsupp (fun v _ _ =>
            add_nonneg (by exact_mod_cast heff₁ v) (by exact_mod_cast heff₂ v))
      _ = (∑ v ∈ D₁.support ∪ D₂.support, (D₁ v : ℝ))
          + ∑ v ∈ D₁.support ∪ D₂.support, (D₂ v : ℝ) := Finset.sum_add_distrib
      _ ≤ (n : ℝ) + (n : ℝ) := by
          have e₁ : ∑ v ∈ D₁.support ∪ D₂.support, (D₁ v : ℝ) = (n : ℝ) := by
            rw [← (Finset.sum_subset Finset.subset_union_left (fun v _ hv => by
              rw [Finsupp.notMem_support_iff.mp hv]; simp))]
            have h2 : (∑ v ∈ D₁.support, D₁ v) = (n : ℤ) := hsum₁
            exact_mod_cast h2
          have e₂ : ∑ v ∈ D₁.support ∪ D₂.support, (D₂ v : ℝ) = (n : ℝ) := by
            rw [← (Finset.sum_subset Finset.subset_union_right (fun v _ hv => by
              rw [Finsupp.notMem_support_iff.mp hv]; simp))]
            have h2 : (∑ v ∈ D₂.support, D₂ v) = (n : ℤ) := hsum₂
            exact_mod_cast h2
          rw [e₁, e₂]
      _ = 2 * (n : ℝ) := by ring

  have hcm : c * mass ≤ |c| * mass :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hmass0

  have hA₂mem : ∀ v ∈ (D₂.erase o).support, v ≠ o := by
    intro v hv
    rw [Finsupp.support_erase] at hv
    exact (Finset.mem_erase.mp hv).1
  have hA₂val : ∀ v ∈ (D₂.erase o).support, ((D₂.erase o) v : ℝ) = (D₂ v : ℝ) := by
    intro v hv
    rw [Finsupp.erase_ne (hA₂mem v hv)]
  have hQmem : ∀ v ∈ (P.erase o).support, v ≠ o := by
    intro v hv
    rw [Finsupp.support_erase] at hv
    exact (Finset.mem_erase.mp hv).1
  have hQval : ∀ v ∈ (P.erase o).support, ((P.erase o) v : ℝ) = (P v : ℝ) := by
    intro v hv
    rw [Finsupp.erase_ne (hQmem v hv)]

  have hŜnonneg : ∀ (E : X →₀ ℤ), (∀ w, 0 ≤ E w) →
      0 ≤ (E.erase o).sum fun v m => (m : ℝ) * pt v := by
    intro E hE
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun v hv => mul_nonneg ?_ (hpt v)
    rw [Finsupp.erase_ne ?_]
    · exact_mod_cast hE v
    · rw [Finsupp.support_erase] at hv
      exact (Finset.mem_erase.mp hv).1

  have hsumD₁A₂ : ∑ v ∈ (D₂.erase o).support, (D₁ v : ℝ) * pt v
      ≤ (D₁.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (D₂.erase o).support, (D₁ v : ℝ) * pt v
        = ∑ v ∈ (D₂.erase o).support, ((D₁.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hA₂mem v hv)]
      _ ≤ _ := wsum_le o hpt heff₁ _
  have hsumD₂A₂ : ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * pt v
      ≤ (D₂.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * pt v
        = ∑ v ∈ (D₂.erase o).support, ((D₂.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hA₂mem v hv)]
      _ ≤ _ := wsum_le o hpt heff₂ _
  have hsumD₁Q : ∑ v ∈ (P.erase o).support, (D₁ v : ℝ) * pt v
      ≤ (D₁.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (P.erase o).support, (D₁ v : ℝ) * pt v
        = ∑ v ∈ (P.erase o).support, ((D₁.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hQmem v hv)]
      _ ≤ _ := wsum_le o hpt heff₁ _
  have hsumD₂Q : ∑ v ∈ (P.erase o).support, (D₂ v : ℝ) * pt v
      ≤ (D₂.erase o).sum fun v m => (m : ℝ) * pt v := by
    calc ∑ v ∈ (P.erase o).support, (D₂ v : ℝ) * pt v
        = ∑ v ∈ (P.erase o).support, ((D₂.erase o) v : ℝ) * pt v :=
          Finset.sum_congr rfl fun v hv => by rw [Finsupp.erase_ne (hQmem v hv)]
      _ ≤ _ := wsum_le o hpt heff₂ _
  set Ŝ₁ : ℝ := (D₁.erase o).sum fun v m => (m : ℝ) * pt v with hŜ₁def
  set Ŝ₂ : ℝ := (D₂.erase o).sum fun v m => (m : ℝ) * pt v with hŜ₂def
  have hŜ₁0 : 0 ≤ Ŝ₁ := hŜnonneg D₁ heff₁
  have hŜ₂0 : 0 ≤ Ŝ₂ := hŜnonneg D₂ heff₂

  have hbranchA : |phiC γ t b (P.erase o) (P o) (D₂.erase o)|
      ≤ ε * ((n : ℝ) * (Ŝ₁ + Ŝ₂)) + (n : ℝ) * (|c| * mass) := by
    calc |phiC γ t b (P.erase o) (P o) (D₂.erase o)|
        ≤ ∑ v ∈ (D₂.erase o).support,
            |((D₂.erase o) v : ℝ)| * |ePt γ t b (P.erase o) (P o) v| :=
          abs_phiC_le γ t b (P.erase o) (P o) (D₂.erase o)
      _ ≤ ∑ v ∈ (D₂.erase o).support,
            (D₂ v : ℝ) * (ε * |(P v : ℝ)| * pt v + c * mass) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hA₂val v hv, abs_of_nonneg (by exact_mod_cast heff₂ v : (0:ℝ) ≤ (D₂ v : ℝ))]
          exact mul_le_mul_of_nonneg_left (hR4 v (hA₂mem v hv))
            (by exact_mod_cast heff₂ v)
      _ = ε * (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * (|(P v : ℝ)| * pt v))
          + (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (c * mass) := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ ε * ((n : ℝ) * (Ŝ₁ + Ŝ₂)) + (n : ℝ) * (|c| * mass) := by
          have h1 : ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * (|(P v : ℝ)| * pt v)
              ≤ (n : ℝ) * (Ŝ₁ + Ŝ₂) := by
            calc ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * (|(P v : ℝ)| * pt v)
                ≤ ∑ v ∈ (D₂.erase o).support,
                    (n : ℝ) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                  refine Finset.sum_le_sum fun v hv => ?_
                  have hD₂0 : (0:ℝ) ≤ (D₂ v : ℝ) := by exact_mod_cast heff₂ v
                  calc (D₂ v : ℝ) * (|(P v : ℝ)| * pt v)
                      ≤ (n : ℝ) * (|(P v : ℝ)| * pt v) :=
                        mul_le_mul_of_nonneg_right (hD₂n v)
                          (mul_nonneg (abs_nonneg _) (hpt v))
                    _ ≤ (n : ℝ) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
                        exact mul_le_mul_of_nonneg_right (hPabs v) (hpt v)
              _ = (n : ℝ) * ((∑ v ∈ (D₂.erase o).support, (D₁ v : ℝ) * pt v)
                  + ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) * pt v) := by
                  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun v _ => by ring
              _ ≤ (n : ℝ) * (Ŝ₁ + Ŝ₂) := by
                  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
                  exact add_le_add hsumD₁A₂ hsumD₂A₂
          have h2 : (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (c * mass)
              ≤ (n : ℝ) * (|c| * mass) := by
            have hw0 : 0 ≤ ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) :=
              Finset.sum_nonneg fun v _ => by exact_mod_cast heff₂ v
            have hwn : ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ) ≤ (n : ℝ) := by
              calc ∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)
                  ≤ ∑ v ∈ D₂.support, (D₂ v : ℝ) := by
                    rw [Finsupp.support_erase]
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.erase_subset o D₂.support)
                      (fun v _ _ => by exact_mod_cast heff₂ v)
                _ = (n : ℝ) := by
                    have h2 : (∑ v ∈ D₂.support, D₂ v) = (n : ℤ) := hsum₂
                    exact_mod_cast h2
            calc (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (c * mass)
                ≤ (∑ v ∈ (D₂.erase o).support, (D₂ v : ℝ)) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_left hcm hw0
              _ ≤ (n : ℝ) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_right hwn (mul_nonneg (abs_nonneg _) hmass0)
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (le_of_lt hε)) h2

  have hbranchQ : |phiC γ t b (P.erase o) (P o) (P.erase o)|
      ≤ ε * ((2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂)) + (2 * (n : ℝ)) * (|c| * mass) := by
    calc |phiC γ t b (P.erase o) (P o) (P.erase o)|
        ≤ ∑ v ∈ (P.erase o).support,
            |((P.erase o) v : ℝ)| * |ePt γ t b (P.erase o) (P o) v| :=
          abs_phiC_le γ t b (P.erase o) (P o) (P.erase o)
      _ ≤ ∑ v ∈ (P.erase o).support,
            |(P v : ℝ)| * (ε * |(P v : ℝ)| * pt v + c * mass) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [hQval v hv]
          exact mul_le_mul_of_nonneg_left (hR4 v (hQmem v hv)) (abs_nonneg _)
      _ = ε * (∑ v ∈ (P.erase o).support, |(P v : ℝ)| * (|(P v : ℝ)| * pt v))
          + (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (c * mass) := by
          rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ ε * ((2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂)) + (2 * (n : ℝ)) * (|c| * mass) := by
          have h1 : ∑ v ∈ (P.erase o).support, |(P v : ℝ)| * (|(P v : ℝ)| * pt v)
              ≤ (2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂) := by
            calc ∑ v ∈ (P.erase o).support, |(P v : ℝ)| * (|(P v : ℝ)| * pt v)
                ≤ ∑ v ∈ (P.erase o).support,
                    (2 * (n : ℝ)) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                  refine Finset.sum_le_sum fun v hv => ?_
                  have hP2n : |(P v : ℝ)| ≤ 2 * (n : ℝ) :=
                    (hPabs v).trans (by linarith [hD₁n v, hD₂n v])
                  calc |(P v : ℝ)| * (|(P v : ℝ)| * pt v)
                      ≤ (2 * (n : ℝ)) * (|(P v : ℝ)| * pt v) :=
                        mul_le_mul_of_nonneg_right hP2n
                          (mul_nonneg (abs_nonneg _) (hpt v))
                    _ ≤ (2 * (n : ℝ)) * (((D₁ v : ℝ) + (D₂ v : ℝ)) * pt v) := by
                        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                        exact mul_le_mul_of_nonneg_right (hPabs v) (hpt v)
              _ = (2 * (n : ℝ)) * ((∑ v ∈ (P.erase o).support, (D₁ v : ℝ) * pt v)
                  + ∑ v ∈ (P.erase o).support, (D₂ v : ℝ) * pt v) := by
                  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  exact Finset.sum_congr rfl fun v _ => by ring
              _ ≤ (2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact add_le_add hsumD₁Q hsumD₂Q
          have h2 : (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (c * mass)
              ≤ (2 * (n : ℝ)) * (|c| * mass) := by
            have hw0 : 0 ≤ ∑ v ∈ (P.erase o).support, |(P v : ℝ)| :=
              Finset.sum_nonneg fun v _ => abs_nonneg _
            have hwm : ∑ v ∈ (P.erase o).support, |(P v : ℝ)| ≤ mass := by
              rw [hmass, Finsupp.sum]
              calc ∑ v ∈ (P.erase o).support, |(P v : ℝ)|
                  ≤ ∑ v ∈ P.support, |(P v : ℝ)| := by
                    rw [Finsupp.support_erase]
                    exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.erase_subset o P.support) (fun v _ _ => abs_nonneg _)
                _ = ∑ v ∈ P.support, |(P v : ℝ)| := rfl
            calc (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (c * mass)
                ≤ (∑ v ∈ (P.erase o).support, |(P v : ℝ)|) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_left hcm hw0
              _ ≤ mass * (|c| * mass) :=
                  mul_le_mul_of_nonneg_right hwm (mul_nonneg (abs_nonneg _) hmass0)
              _ ≤ (2 * (n : ℝ)) * (|c| * mass) :=
                  mul_le_mul_of_nonneg_right hmass2n
                    (mul_nonneg (abs_nonneg _) hmass0)
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (le_of_lt hε)) h2

  have hεn' : ε * (n : ℝ) ≤ ε₀ := by
    have : ε * (n : ℝ) ≤ ε * ((n : ℝ) + 1) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hε)
    linarith
  have hŜsum : Ŝ₁ + Ŝ₂ ≤ (B * h₁ + C₁) + (B * h₂ + C₁) := add_le_add hS₁ hS₂
  have hεpart : 2 * (ε * (n : ℝ)) * (Ŝ₁ + Ŝ₂) ≤ 2 * ε₀ * (Ŝ₁ + Ŝ₂) := by
    have h0 : 0 ≤ Ŝ₁ + Ŝ₂ := add_nonneg hŜ₁0 hŜ₂0
    nlinarith [hεn', h0]
  have hmasscm : |c| * mass ≤ |c| * (2 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hmass2n (abs_nonneg c)
  calc phiC γ t b (P.erase o) (P o) (D₂.erase o)
      + (1 / 2) * phiC γ t b (P.erase o) (P o) (P.erase o)
      ≤ |phiC γ t b (P.erase o) (P o) (D₂.erase o)|
        + (1 / 2) * |phiC γ t b (P.erase o) (P o) (P.erase o)| := by
        have := le_abs_self (phiC γ t b (P.erase o) (P o) (D₂.erase o))
        have := le_abs_self (phiC γ t b (P.erase o) (P o) (P.erase o))
        linarith
    _ ≤ (ε * ((n : ℝ) * (Ŝ₁ + Ŝ₂)) + (n : ℝ) * (|c| * mass))
        + (1 / 2) * (ε * ((2 * (n : ℝ)) * (Ŝ₁ + Ŝ₂)) + (2 * (n : ℝ)) * (|c| * mass)) := by
        have h2 : (0:ℝ) ≤ 1 / 2 := by norm_num
        linarith [hbranchA, mul_le_mul_of_nonneg_left hbranchQ h2]
    _ = 2 * (ε * (n : ℝ)) * (Ŝ₁ + Ŝ₂) + 2 * (n : ℝ) * (|c| * mass) := by ring
    _ ≤ 2 * ε₀ * (Ŝ₁ + Ŝ₂) + 2 * (n : ℝ) * (|c| * (2 * (n : ℝ))) := by
        have hn0 : (0:ℝ) ≤ 2 * (n : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hmasscm hn0
        linarith [hεpart]
    _ ≤ 2 * ε₀ * ((B * h₁ + C₁) + (B * h₂ + C₁)) + 2 * (n : ℝ) * (|c| * (2 * (n : ℝ))) := by
        have h2ε₀ : (0:ℝ) ≤ 2 * ε₀ := by positivity
        have := mul_le_mul_of_nonneg_left hŜsum h2ε₀
        linarith
    _ = 2 * ε₀ * B * (h₁ + h₂) + (4 * ε₀ * C₁ + 4 * (n : ℝ) ^ 2 * |c|) := by ring

end B0Arith

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le.ModularCurve AlgebraicCurve"

namespace B0R8

private theorem absLogHeight_eq_of_range_eq {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (S : Set (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ (IntermediateField.adjoin ℚ S)] (hS : Set.range x = S) :
    absLogHeight x
      = (Module.finrank ℚ (IntermediateField.adjoin ℚ S) : ℝ)⁻¹ *
          Height.logHeight fun i =>
            (⟨x i, hS ▸ IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩⟩ :
              IntermediateField.adjoin ℚ S) := by
  subst hS
  rfl

private theorem absLogHeight_comp_equiv {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (y : ι' → AlgebraicClosure ℚ) :
    absLogHeight (y ∘ ⇑e) = absLogHeight y := by
  haveI := finiteDimensional_adjoin_range y
  have hrange : Set.range (y ∘ ⇑e) = Set.range y := e.surjective.range_comp y
  rw [absLogHeight_eq_of_range_eq (y ∘ ⇑e) (Set.range y) hrange,
    absLogHeight_eq_of_range_eq y (Set.range y) rfl]
  exact congrArg _ (Height.logHeight_comp_equiv e
    (fun i' => (⟨y i', IntermediateField.subset_adjoin ℚ (Set.range y) ⟨i', rfl⟩⟩ :
      IntermediateField.adjoin ℚ (Set.range y))))

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

private theorem chordVec_swap {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    chordVec s w v = chordVec s v w ∘ ⇑(Equiv.prodComm (Fin r) (Fin r)) := by
  funext p
  simp only [chordVec, Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap,
    Prod.snd_swap]
  ring

private theorem _root_.B0R8.subrow_R8 {r : ℕ}
    (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w = pairHt s w v := by
  unfold pairHt
  rw [chordVec_swap s v w,
    absLogHeight_comp_equiv (Equiv.prodComm (Fin r) (Fin r)) (chordVec s v w)]
  ring

p2m_export "B0R8" "subrow_R8"
end B0R8

namespace ModularCurve p2m_export "ModularCurve" "IsEmbBasis JZero.heightForm JZero.IsRepOf divNaiveHeight divNaiveHeight_nonneg cuspInftyBar modularFunctionFieldBar JZero JZero.ptsum_pointHt_le_divNaiveHeight deg_eq_one_modularFunctionFieldBar JZero.pairing_principal_le_of_prime_of_five_le" namespace JZero p2m_export "ModularCurve.JZero" "heightForm IsRepOf ptsum_pointHt_le_divNaiveHeight pairing_principal_le_of_prime_of_five_le" end ModularCurve.JZero
p2m_open_scoped "ModularCurve ModularCurve.JZero" in
open Classical in

private theorem ModularCurve.JZero.pairing_eq_ePt (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ((A.erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
        + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
          * (A v : ℝ) * baseHt s (cuspInftyBar N) v
      = B0R1.ePt (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ)
          (baseHt s (cuspInftyBar N)) (pairHt s) (A.erase (cuspInftyBar N))
          (A (cuspInftyBar N)) v := by
  have ht0 : baseHt s (cuspInftyBar N) (cuspInftyBar N) = 0 := by
    unfold baseHt
    exact if_pos rfl
  simp only [B0R1.ePt, Int.cast_natCast]
  rw [Finsupp.sum, Finsupp.support_erase, Finsupp.support_erase]
  have h1 : ∑ w ∈ A.support.erase v,
        ((A.erase v) w : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w)
      = ∑ w ∈ A.support.erase v, (A w : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w) :=
    Finset.sum_congr rfl fun w hw => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]
  have h2 : ∑ w ∈ (A.support.erase (cuspInftyBar N)).erase v,
        ((A.erase (cuspInftyBar N)) w : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w)
      = ∑ w ∈ (A.support.erase (cuspInftyBar N)).erase v,
        (A w : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w) :=
    Finset.sum_congr rfl fun w hw => by
      rw [Finsupp.erase_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw))]
  rw [h1, h2]
  by_cases hv : v = cuspInftyBar N
  · subst hv
    rw [Finset.erase_idem, ht0, Finsupp.erase_same]
    simp
  · have htv : baseHt s (cuspInftyBar N) v = pairHt s v (cuspInftyBar N) := by
      unfold baseHt
      exact if_neg hv
    rw [Finsupp.erase_ne hv, Finset.erase_right_comm]
    by_cases ho : cuspInftyBar N ∈ A.support.erase v
    · rw [← Finset.add_sum_erase (A.support.erase v)
        (fun w => (A w : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w)) ho, ht0, htv]
      ring
    · have hAo : A (cuspInftyBar N) = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro h
        exact ho (Finset.mem_erase.mpr ⟨fun h' => hv h'.symm, h⟩)
      rw [Finset.erase_eq_of_notMem ho, hAo]
      simp

namespace B0Asm

open B0R1

private theorem abs_phiC_le {X : Type} [DecidableEq X] (γ : ℤ) (t : X → ℝ) (b : X → X → ℝ)
    (Q : X →₀ ℤ) (c : ℤ) (A : X →₀ ℤ) :
    |phiC γ t b Q c A| ≤ ∑ v ∈ A.support, |(A v : ℝ)| * |ePt γ t b Q c v| :=
  (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun _ _ => abs_mul _ _)

private theorem _root_.B0Asm.subrow_R8 {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w = pairHt s w v :=
  B0R8.subrow_R8 s v w

p2m_export "B0Asm" "subrow_R8"

private theorem deg_one (N : ℕ) [NeZero N]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.deg = 1 :=
  ModularCurve.deg_eq_one_modularFunctionFieldBar N v

private theorem subrow_R2 (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {n : ℕ} {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h₁ : JZero.IsRepOf N K n c D₁) (h₂ : JZero.IsRepOf N K n c D₂) :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        D₁ v - D₂ v = v.ord f := by
  obtain ⟨E₁, hD₁, hsh₁, hst₁, hc₁⟩ := h₁
  obtain ⟨E₂, hD₂, hsh₂, hst₂, hc₂⟩ := h₂
  have hmk : Pic0.mk E₁ = Pic0.mk E₂ := by rw [hc₁, hc₂]
  have hmem : -E₁ + E₂ ∈ (Divisor.principal (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar N))).addSubgroupOf
      (Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))) :=
    QuotientAddGroup.eq.mp hmk
  have hprin : ((-E₁ + E₂ : Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar N))) :
        Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    AddSubgroup.mem_addSubgroupOf.mp hmem
  obtain ⟨g, hg0, hg⟩ := Divisor.mem_principal.mp hprin
  refine ⟨g⁻¹, inv_ne_zero hg0, fun v => ?_⟩
  have hgv := hg v
  simp only [AddSubgroup.coe_add, NegMemClass.coe_neg, Finsupp.add_apply,
    Finsupp.neg_apply] at hgv
  rw [v.ord_inv, ← hsh₁, ← hsh₂]
  simp only [Finsupp.add_apply]
  linarith [hgv]

private theorem IsRepOf.coeffSum (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {n : ℕ} {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : JZero.IsRepOf N K n c D) :
    (D.sum fun _ m => m) = (n : ℤ) := by
  obtain ⟨E, hD, hsh, hst, hc⟩ := h
  have hdegE : Divisor.degree (E : Divisor (AlgebraicClosure ℚ)
      (modularFunctionFieldBar N)) = 0 := E.2
  have hdeg_eq_sum : ∀ A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Divisor.degree A = A.sum fun _ m => m := by
    intro A
    conv_lhs => rw [← Finsupp.sum_single A]
    rw [map_finsuppSum]
    refine Finsupp.sum_congr fun v _ => ?_
    rw [Divisor.degree_single, deg_one N v]
    simp
  have hsum_add : ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        + (n : ℤ) • Finsupp.single (cuspInftyBar N) 1).sum (fun _ m => m)
      = ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).sum fun _ m => m)
        + (((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)).sum fun _ m => m) :=
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have hsingle : (((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)).sum fun _ m => m)
      = (n : ℤ) := by
    rw [Finsupp.smul_single, Finsupp.sum_single_index rfl]
    simp
  have hE0 : ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).sum
      fun _ m => m) = 0 := by rw [← hdeg_eq_sum]; exact hdegE
  rw [← hsh, hsum_add, hsingle, hE0, zero_add]

private theorem IsRepOf.apply_le (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {n : ℕ} {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : JZero.IsRepOf N K n c D)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : D v ≤ (n : ℤ) := by
  have heff : ∀ w, 0 ≤ D w := h.choose_spec.1
  by_cases hv : v ∈ D.support
  · calc D v ≤ ∑ w ∈ D.support, D w :=
          Finset.single_le_sum (fun w _ => heff w) hv
      _ = (n : ℤ) := IsRepOf.coeffSum N K h
  · rw [Finsupp.notMem_support_iff.mp hv]
    exact_mod_cast Nat.zero_le n

private theorem pointHt_nonneg {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v := by
  haveI := finiteDimensional_adjoin_range (evalVec s v)
  unfold pointHt absLogHeight
  exact mul_nonneg (by positivity) (Height.logHeight_nonneg _)

private theorem divNaiveHeight_nonneg (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (n : ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ divNaiveHeight N K n D := by
  classical
  unfold divNaiveHeight
  split
  · exact Height.logHeight_nonneg _
  · exact le_refl 0

private theorem erase_sub {X : Type} [DecidableEq X] (o : X) (f g : X →₀ ℤ) :
    (f - g).erase o = f.erase o - g.erase o := by
  ext v
  by_cases hv : v = o
  · subst hv; simp [Finsupp.erase_same]
  · simp [Finsupp.erase_ne hv]

private theorem _root_.B0Asm.subrow_ARITH {X : Type} [DecidableEq X] (o : X) (γ : ℤ) (t : X → ℝ)
    (b : X → X → ℝ) (pt : X → ℝ) (D₁ D₂ : X →₀ ℤ) (n : ℕ)
    (heff₁ : ∀ w, 0 ≤ D₁ w) (heff₂ : ∀ w, 0 ≤ D₂ w)
    (hsum₁ : (D₁.sum fun _ m => m) = (n : ℤ)) (hsum₂ : (D₂.sum fun _ m => m) = (n : ℤ))
    (hpt : ∀ v, 0 ≤ pt v)
    (ε c B C₁ h₁ h₂ : ℝ) (hε : 0 < ε) (hεn : ε * ((n : ℝ) + 1) ≤ 1) (hB0 : 0 ≤ B)
    (hR4 : ∀ v, v ≠ o →
      |ePt γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) v|
        ≤ ε * |((D₁ - D₂) v : ℝ)| * pt v + c * ((D₁ - D₂).sum fun _ m => |(m : ℝ)|))
    (hS₁ : ((D₁.erase o).sum fun v m => (m : ℝ) * pt v) ≤ B * h₁ + C₁)
    (hS₂ : ((D₂.erase o).sum fun v m => (m : ℝ) * pt v) ≤ B * h₂ + C₁) :
    phiC γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) (D₂.erase o)
      + (1 / 2) * phiC γ t b ((D₁ - D₂).erase o) ((D₁ - D₂) o) ((D₁ - D₂).erase o)
      ≤ 2 * B * (h₁ + h₂) + (4 * C₁ + 4 * (n : ℝ) ^ 2 * |c|) :=
  B0Arith.subrow_ARITH o γ t b pt D₁ D₂ n heff₁ heff₂ hsum₁ hsum₂ hpt
    ε c B C₁ h₁ h₂ hε hεn hB0 hR4 hS₁ hS₂

p2m_export "B0Asm" "subrow_ARITH"

private theorem assembly (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ n : ℕ, ∃ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      JZero.IsRepOf N K n c D₁ → JZero.IsRepOf N K n c D₂ →
      JZero.heightForm N s D₁ ≤ JZero.heightForm N s D₂
        + c₀ * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂) + C := by
  classical
  obtain ⟨B, hB0, hPTS⟩ := JZero.ptsum_pointHt_le_divNaiveHeight N K s hs
  refine ⟨2 * B, fun n => ?_⟩
  have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨c, hR4⟩ := ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le N hN hN5 s hs
    (1 / ((n : ℝ) + 1)) hεpos
  obtain ⟨C₁, hPTSn⟩ := hPTS n
  refine ⟨4 * C₁ + 4 * (n : ℝ) ^ 2 * |c|, fun cc D₁ D₂ h₁ h₂ => ?_⟩
  obtain ⟨f, hf0, hdiv⟩ := subrow_R2 N K h₁ h₂
  have hPord : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (D₁ - D₂) w = w.ord f := fun w => by
    rw [Finsupp.sub_apply]; exact hdiv w

  have hcast : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (D.sum fun _ m => (m : ℝ)) = ((D.sum fun _ m => m : ℤ) : ℝ) := by
    intro D
    simp only [Finsupp.sum]
    push_cast
    ring
  have hPsum : ((D₁ - D₂).sum fun _ m => (m : ℝ)) = 0 := by
    rw [Finsupp.sum_sub_index (fun a b₁ b₂ => by push_cast; ring), hcast D₁, hcast D₂,
      IsRepOf.coeffSum N K h₁, IsRepOf.coeffSum N K h₂]
    simp

  have hsplitsum : (((D₁ - D₂).erase (cuspInftyBar N)).sum fun _ m => (m : ℝ))
      = ((D₁ - D₂).sum fun _ m => (m : ℝ)) - (((D₁ - D₂) (cuspInftyBar N) : ℤ) : ℝ) := by
    simp only [Finsupp.sum, Finsupp.support_erase]
    rw [Finset.sum_congr rfl (fun w hw => by
      rw [Finsupp.erase_ne (Finset.mem_erase.mp hw).1])]
    exact B0R1.sum_erase_deg (D₁ - D₂) (cuspInftyBar N)
  have hres : (((D₁ - D₂).erase (cuspInftyBar N)).sum fun _ m => (m : ℝ))
      + (((D₁ - D₂) (cuspInftyBar N) : ℤ) : ℝ) = 0 := by
    rw [hsplitsum, hPsum]; ring

  have hsplit : D₁.erase (cuspInftyBar N)
      = D₂.erase (cuspInftyBar N) + (D₁ - D₂).erase (cuspInftyBar N) := by
    rw [erase_sub]; abel

  have hreg := B0R1.regroup (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (baseHt s (cuspInftyBar N)) (pairHt s) (fun v w => subrow_R8 s v w)
    (D₂.erase (cuspInftyBar N)) ((D₁ - D₂).erase (cuspInftyBar N))
    ((D₁ - D₂) (cuspInftyBar N))

  have hb₁ : JZero.heightForm N s D₁
      = B0R1.auxAbs (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (baseHt s (cuspInftyBar N)) (pairHt s) (D₁.erase (cuspInftyBar N)) := rfl
  have hb₂ : JZero.heightForm N s D₂
      = B0R1.auxAbs (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (baseHt s (cuspInftyBar N)) (pairHt s) (D₂.erase (cuspInftyBar N)) := rfl

  have hΔ : JZero.heightForm N s D₁
      = JZero.heightForm N s D₂
        + (phiC (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            (baseHt s (cuspInftyBar N)) (pairHt s)
            ((D₁ - D₂).erase (cuspInftyBar N)) ((D₁ - D₂) (cuspInftyBar N))
            (D₂.erase (cuspInftyBar N))
          + (1 / 2) * phiC (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
              (baseHt s (cuspInftyBar N)) (pairHt s)
              ((D₁ - D₂).erase (cuspInftyBar N)) ((D₁ - D₂) (cuspInftyBar N))
              ((D₁ - D₂).erase (cuspInftyBar N))) := by
    rw [hb₁, hb₂, hsplit, hreg, hres, zero_mul, add_zero]
    ring

  have hεn : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) ≤ 1 :=
    le_of_eq (one_div_mul_cancel (by positivity : ((n : ℝ) + 1) ≠ 0))
  have harith := subrow_ARITH (cuspInftyBar N)
    (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (baseHt s (cuspInftyBar N)) (pairHt s) (pointHt s) D₁ D₂ n
    h₁.choose_spec.1 h₂.choose_spec.1
    (IsRepOf.coeffSum N K h₁) (IsRepOf.coeffSum N K h₂)
    (fun v => pointHt_nonneg s v)
    (1 / ((n : ℝ) + 1)) c B C₁
    (divNaiveHeight N K n D₁) (divNaiveHeight N K n D₂)
    hεpos hεn hB0
    (fun v _ => by
      have h := hR4 f (D₁ - D₂) hPord v
      rwa [ModularCurve.JZero.pairing_eq_ePt N s (D₁ - D₂) v] at h)
    (hPTSn cc D₁ h₁) (hPTSn cc D₂ h₂)
  linarith [hΔ, harith]

private theorem assembly_eps (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ n : ℕ, ∃ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      JZero.IsRepOf N K n c D₁ → JZero.IsRepOf N K n c D₂ →
      JZero.heightForm N s D₁ ≤ JZero.heightForm N s D₂
        + ε₀ * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂) + C := by
  classical
  obtain ⟨B, hB0, hPTS⟩ := JZero.ptsum_pointHt_le_divNaiveHeight N K s hs
  intro ε₀ hε₀ n
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have hε₀'pos : (0 : ℝ) < ε₀ / (2 * (B + 1)) := by positivity
  have hεpos : (0 : ℝ) < ε₀ / (2 * (B + 1)) / ((n : ℝ) + 1) := by positivity
  obtain ⟨c, hR4⟩ := ModularCurve.JZero.pairing_principal_le_of_prime_of_five_le N hN hN5 s hs
    (ε₀ / (2 * (B + 1)) / ((n : ℝ) + 1)) hεpos
  obtain ⟨C₁, hPTSn⟩ := hPTS n
  refine ⟨4 * (ε₀ / (2 * (B + 1))) * C₁ + 4 * (n : ℝ) ^ 2 * |c|, fun cc D₁ D₂ h₁ h₂ => ?_⟩
  obtain ⟨f, hf0, hdiv⟩ := subrow_R2 N K h₁ h₂
  have hPord : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (D₁ - D₂) w = w.ord f := fun w => by
    rw [Finsupp.sub_apply]; exact hdiv w

  have hcast : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (D.sum fun _ m => (m : ℝ)) = ((D.sum fun _ m => m : ℤ) : ℝ) := by
    intro D
    simp only [Finsupp.sum]
    push_cast
    ring
  have hPsum : ((D₁ - D₂).sum fun _ m => (m : ℝ)) = 0 := by
    rw [Finsupp.sum_sub_index (fun a b₁ b₂ => by push_cast; ring), hcast D₁, hcast D₂,
      IsRepOf.coeffSum N K h₁, IsRepOf.coeffSum N K h₂]
    simp

  have hsplitsum : (((D₁ - D₂).erase (cuspInftyBar N)).sum fun _ m => (m : ℝ))
      = ((D₁ - D₂).sum fun _ m => (m : ℝ)) - (((D₁ - D₂) (cuspInftyBar N) : ℤ) : ℝ) := by
    simp only [Finsupp.sum, Finsupp.support_erase]
    rw [Finset.sum_congr rfl (fun w hw => by
      rw [Finsupp.erase_ne (Finset.mem_erase.mp hw).1])]
    exact B0R1.sum_erase_deg (D₁ - D₂) (cuspInftyBar N)
  have hres : (((D₁ - D₂).erase (cuspInftyBar N)).sum fun _ m => (m : ℝ))
      + (((D₁ - D₂) (cuspInftyBar N) : ℤ) : ℝ) = 0 := by
    rw [hsplitsum, hPsum]; ring

  have hsplit : D₁.erase (cuspInftyBar N)
      = D₂.erase (cuspInftyBar N) + (D₁ - D₂).erase (cuspInftyBar N) := by
    rw [erase_sub]; abel

  have hreg := B0R1.regroup (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (baseHt s (cuspInftyBar N)) (pairHt s) (fun v w => subrow_R8 s v w)
    (D₂.erase (cuspInftyBar N)) ((D₁ - D₂).erase (cuspInftyBar N))
    ((D₁ - D₂) (cuspInftyBar N))

  have hb₁ : JZero.heightForm N s D₁
      = B0R1.auxAbs (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (baseHt s (cuspInftyBar N)) (pairHt s) (D₁.erase (cuspInftyBar N)) := rfl
  have hb₂ : JZero.heightForm N s D₂
      = B0R1.auxAbs (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (baseHt s (cuspInftyBar N)) (pairHt s) (D₂.erase (cuspInftyBar N)) := rfl

  have hΔ : JZero.heightForm N s D₁
      = JZero.heightForm N s D₂
        + (phiC (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            (baseHt s (cuspInftyBar N)) (pairHt s)
            ((D₁ - D₂).erase (cuspInftyBar N)) ((D₁ - D₂) (cuspInftyBar N))
            (D₂.erase (cuspInftyBar N))
          + (1 / 2) * phiC (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
              (baseHt s (cuspInftyBar N)) (pairHt s)
              ((D₁ - D₂).erase (cuspInftyBar N)) ((D₁ - D₂) (cuspInftyBar N))
              ((D₁ - D₂).erase (cuspInftyBar N))) := by
    rw [hb₁, hb₂, hsplit, hreg, hres, zero_mul, add_zero]
    ring
  have hεn : (ε₀ / (2 * (B + 1)) / ((n : ℝ) + 1)) * ((n : ℝ) + 1) ≤ ε₀ / (2 * (B + 1)) :=
    le_of_eq (div_mul_cancel₀ (ε₀ / (2 * (B + 1))) (by positivity : ((n : ℝ) + 1) ≠ 0))
  have harith := B0Arith.subrow_ARITH_eps (cuspInftyBar N)
    (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (baseHt s (cuspInftyBar N)) (pairHt s) (pointHt s) D₁ D₂ n
    h₁.choose_spec.1 h₂.choose_spec.1
    (IsRepOf.coeffSum N K h₁) (IsRepOf.coeffSum N K h₂)
    (fun v => pointHt_nonneg s v)
    (ε₀ / (2 * (B + 1)) / ((n : ℝ) + 1)) c B C₁
    (divNaiveHeight N K n D₁) (divNaiveHeight N K n D₂) (ε₀ / (2 * (B + 1)))
    hεpos hε₀'pos hεn hB0
    (fun v _ => by
      have h := hR4 f (D₁ - D₂) hPord v
      rwa [ModularCurve.JZero.pairing_eq_ePt N s (D₁ - D₂) v] at h)
    (hPTSn cc D₁ h₁) (hPTSn cc D₂ h₂)
  have hdnh : (0 : ℝ) ≤ divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂ :=
    add_nonneg (divNaiveHeight_nonneg N K n D₁) (divNaiveHeight_nonneg N K n D₂)
  have hslope : 2 * (ε₀ / (2 * (B + 1))) * B ≤ ε₀ := by
    rw [show 2 * (ε₀ / (2 * (B + 1))) * B = ε₀ * (B / (B + 1)) from by
      field_simp]
    calc ε₀ * (B / (B + 1)) ≤ ε₀ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hε₀.le
          rw [div_le_one hB1]
          linarith
      _ = ε₀ := mul_one ε₀
  have hmono : 2 * (ε₀ / (2 * (B + 1))) * B * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂)
      ≤ ε₀ * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂) :=
    mul_le_mul_of_nonneg_right hslope hdnh
  linarith [hΔ, harith, hmono]

end B0Asm

end

#check @ModularCurve.JZero.pairing_eq_ePt
#check @B0Asm.subrow_R8
#check @B0Asm.subrow_ARITH
#print axioms B0Asm.subrow_R8
#print axioms B0Asm.subrow_ARITH
#print axioms ModularCurve.JZero.pairing_eq_ePt
#print axioms B0Asm.subrow_R2
#print axioms B0Asm.IsRepOf.coeffSum

p2m_open "ModularCurve P2MW.S_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le.ModularCurve AlgebraicCurve"

theorem solution (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ n : ℕ, ∃ C : ℝ, ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D₁ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      JZero.IsRepOf N K n c D₁ → JZero.IsRepOf N K n c D₂ →
      JZero.heightForm N s D₁ ≤ JZero.heightForm N s D₂
        + c₀ * (divNaiveHeight N K n D₁ + divNaiveHeight N K n D₂) + C :=
  B0Asm.assembly N hN hN5 K s hs

end S_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_JZero_heightForm_quasiInvariant_of_prime_of_five_le (solution)
