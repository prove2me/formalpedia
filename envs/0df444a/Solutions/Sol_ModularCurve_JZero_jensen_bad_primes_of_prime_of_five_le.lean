-- Prove2me | solution 1 for ModularCurve.JZero.jensen_bad_primes_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0ae8e3a3-5b3a-5fad-abfb-2fd6fc981549

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_ModularCurve_JZero_jensen_bad_at_of_prime_of_five_le
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq
import Theorems.Thm_NumberField_FinitePlace_exists_finitePlace_inclusion_eq_rpow
import Theorems.Thm_ModularCurve_JZero_exists_regVal_chord_ne_zero
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_bad_primes_of_prime_of_five_le
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.MultCovering.instAlgebraFbar ModularCurve.MultCovering.instFieldFbar ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.LevelOnePhi.instAddCommGroup instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.jqNModC_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.MultCovering.ssValue_edgeOf ModularCurve.MultCovering.ChartCtx.mk.sizeOf_spec ModularCurve.MultCovering.ChartCtx.mk.injEq ModularCurve.MultCovering.chart_one ModularCurve.MultCovering.chart_zero AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.MultCovering.AnnCtx.mk.sizeOf_spec ModularCurve.MultCovering.AnnCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.sizeOf_spec ModularCurve.MultCovering.FamCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.MultCovering.FamCtx.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_jensen_bad_primes_of_prime_of_five_le.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "embDivisor IsEmbBasis numberField_of_finiteDimensional cuspInftyBar modularFunctionFieldBar JZero JZero.jensen_bad_at_of_prime_of_five_le hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar JZero.exists_regVal_chord_ne_zero"
namespace JZero
p2m_export "ModularCurve.JZero" "jensen_bad_at_of_prime_of_five_le exists_regVal_chord_ne_zero"
namespace BadPrimes
p2m_open "ModularCurve.JZero ModularCurve"

private theorem log_rpow_of_nonneg {a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    Real.log (a ^ d) = d * Real.log a := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow hd.ne', Real.log_zero, mul_zero]
  · exact Real.log_rpow h d

private theorem iSup_rpow_eq {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {d : ℝ} (hd : 0 < d) :
    (⨆ i, f i ^ d) = (⨆ i, f i) ^ d := by
  cases isEmpty_or_nonempty ι with
  | inl _ => rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.zero_rpow hd.ne']
  | inr _ =>
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := f)
    have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
    have hb' : BddAbove (Set.range fun i => f i ^ d) := (Set.finite_range _).bddAbove
    refine le_antisymm (ciSup_le fun i => Real.rpow_le_rpow (hf i) (le_ciSup hb i) hd.le) ?_
    calc (⨆ i, f i) ^ d = f i₀ ^ d := by rw [hi₀]
      _ ≤ ⨆ i, f i ^ d := le_ciSup hb' i₀

private theorem log_iSup_rpow {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {d : ℝ} (hd : 0 < d) :
    Real.log (⨆ i, f i ^ d) = d * Real.log (⨆ i, f i) := by
  rw [iSup_rpow_eq f hf hd, log_rpow_of_nonneg (Real.iSup_nonneg hf) hd]

private theorem abs_log_iSup_le {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
    (ν : NumberField.FinitePlace K) (z : ι → K) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i) {P : ℝ} (hP : 0 ≤ P)
    (h : ∀ i, |Real.log (ν (z i))| ≤ C i * P) :
    |Real.log (⨆ i, ν (z i))| ≤ (∑ i, C i) * P := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    rw [Real.iSup_of_isEmpty, Real.log_zero, abs_zero]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => hC i) hP
  | inr _ =>
    obtain ⟨i₀, hi₀⟩ := exists_eq_ciSup_of_finite (f := fun i => ν (z i))
    rw [← hi₀]
    calc |Real.log (ν (z i₀))| ≤ C i₀ * P := h i₀
      _ ≤ (∑ i, C i) * P :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ i₀)) hP

private theorem assemble_off {S S' X X' A A' Y' m d k P P' β c₀ c : ℝ} (hd : 0 < d) (hP : 0 ≤ P) (hk : 0 ≤ k)
    (hc : c₀ ≤ c) (hβ : β = 0) (hS : S' = d * S) (hX : X' = d * X) (hA : A' = d * A) (hP' : P' = d * P)
    (hE : |S' - ((k - 2 * β) * X' + β * Y' - A' - m)| ≤ c₀ * k * P') :
    |S - (k * X - A - m / d)| ≤ c * k * P := by
  subst hβ hS hX hA hP'
  have hd' : d ≠ 0 := hd.ne'
  have hE' : |d * (S - (k * X - A - m / d))| ≤ c₀ * k * (d * P) := by
    have heq : d * (S - (k * X - A - m / d)) = d * S - ((k - 2 * 0) * (d * X) + 0 * Y' - d * A - m) := by
      field_simp
      ring
    rw [heq]
    exact hE
  rw [abs_mul, abs_of_pos hd] at hE'
  have h1 : |S - (k * X - A - m / d)| ≤ c₀ * k * P := by
    have h2 : d * |S - (k * X - A - m / d)| ≤ d * (c₀ * k * P) := by linarith
    exact le_of_mul_le_mul_left h2 hd
  calc |S - (k * X - A - m / d)| ≤ c₀ * k * P := h1
    _ ≤ c * k * P := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hk) hP

private theorem assemble_cusp {S S' X X' A A' Y' m d k P P' β c₀ CX CY M : ℝ} (hd : 0 < d) (hP : 0 ≤ P)
    (hk : 0 ≤ k) (hβ : 0 ≤ β) (hβk : β ≤ k * M) (hCX : 0 ≤ CX) (hCY : 0 ≤ CY)
    (hS : S' = d * S) (hX : X' = d * X) (hA : A' = d * A) (hP' : P' = d * P)
    (hE : |S' - ((k - 2 * β) * X' + β * Y' - A' - m)| ≤ c₀ * k * P')
    (hXabs : |X| ≤ CX * P) (hYabs : |Y'| ≤ CY * P') :
    |S - (k * X - A - m / d)| ≤ (max c₀ 0 + M * (2 * CX + CY)) * k * P := by
  subst hS hX hA hP'
  have hd' : d ≠ 0 := hd.ne'
  have hdi : 0 < d⁻¹ := inv_pos.mpr hd
  have hsplit : S - (k * X - A - m / d)
      = d⁻¹ * (d * S - ((k - 2 * β) * (d * X) + β * Y' - d * A - m)) + (-(2 * β * X) + β * (d⁻¹ * Y')) := by
    field_simp
    ring
  have h1 : |d⁻¹ * (d * S - ((k - 2 * β) * (d * X) + β * Y' - d * A - m))| ≤ c₀ * k * P := by
    rw [abs_mul, abs_of_pos hdi]
    calc d⁻¹ * |d * S - ((k - 2 * β) * (d * X) + β * Y' - d * A - m)| ≤ d⁻¹ * (c₀ * k * (d * P)) :=
          mul_le_mul_of_nonneg_left hE hdi.le
      _ = c₀ * k * P := by field_simp
  have hX1 : |2 * β * X| ≤ 2 * β * (CX * P) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * β)]
    exact mul_le_mul_of_nonneg_left hXabs (by positivity)
  have hY1 : |β * (d⁻¹ * Y')| ≤ β * (CY * P) := by
    rw [abs_mul, abs_of_nonneg hβ, abs_mul, abs_of_pos hdi]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    calc d⁻¹ * |Y'| ≤ d⁻¹ * (CY * (d * P)) := mul_le_mul_of_nonneg_left hYabs hdi.le
      _ = CY * P := by field_simp
  have h2 : |-(2 * β * X) + β * (d⁻¹ * Y')| ≤ 2 * β * (CX * P) + β * (CY * P) := by
    calc |-(2 * β * X) + β * (d⁻¹ * Y')| ≤ |-(2 * β * X)| + |β * (d⁻¹ * Y')| := abs_add_le _ _
      _ ≤ 2 * β * (CX * P) + β * (CY * P) := by rw [abs_neg]; exact add_le_add hX1 hY1
  have h3 : c₀ * k * P ≤ max c₀ 0 * k * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hk) hP
  have hQ : 0 ≤ (2 * CX + CY) * P := by positivity
  have h5 : β * ((2 * CX + CY) * P) ≤ (k * M) * ((2 * CX + CY) * P) := mul_le_mul_of_nonneg_right hβk hQ
  rw [hsplit]
  calc |d⁻¹ * (d * S - ((k - 2 * β) * (d * X) + β * Y' - d * A - m)) + (-(2 * β * X) + β * (d⁻¹ * Y'))|
      ≤ |d⁻¹ * (d * S - ((k - 2 * β) * (d * X) + β * Y' - d * A - m))| + |-(2 * β * X) + β * (d⁻¹ * Y')| :=
        abs_add_le _ _
    _ ≤ c₀ * k * P + (2 * β * (CX * P) + β * (CY * P)) := add_le_add h1 h2
    _ = c₀ * k * P + β * ((2 * CX + CY) * P) := by ring
    _ ≤ max c₀ 0 * k * P + (k * M) * ((2 * CX + CY) * P) := add_le_add h3 h5
    _ = (max c₀ 0 + M * (2 * CX + CY)) * k * P := by ring

section Transfer

variable {L L' : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L] [NumberField ↥L']
  (h : L ≤ L') (ν : NumberField.FinitePlace ↥L) (ν' : NumberField.FinitePlace ↥L') {d : ℝ} (hd : 0 < d)
  (hν' : ∀ x : ↥L, ν' (IntermediateField.inclusion h x) = ν x ^ d)
include hd hν'

private theorem log_inclusion (z : ↥L) : Real.log (ν' (IntermediateField.inclusion h z)) = d * Real.log (ν z) := by
  rw [hν', log_rpow_of_nonneg (apply_nonneg ν z) hd]

private theorem log_iSup_inclusion {ι : Type*} [Finite ι] (z : ι → ↥L) :
    Real.log (⨆ i, ν' (IntermediateField.inclusion h (z i))) = d * Real.log (⨆ i, ν (z i)) := by
  simp_rw [hν']
  exact log_iSup_rpow _ (fun i => apply_nonneg ν _) hd

private theorem prox_inclusion {ι : Type*} [Finite ι] (a b : ι → ↥L) :
    prox ν' (fun i => IntermediateField.inclusion h (a i)) (fun i => IntermediateField.inclusion h (b i))
      = d * prox ν a b := by
  have h3 : (fun q : ι × ι => ν' (IntermediateField.inclusion h (a q.1) * IntermediateField.inclusion h (b q.2)
      - IntermediateField.inclusion h (a q.2) * IntermediateField.inclusion h (b q.1)))
      = fun q => ν' (IntermediateField.inclusion h (a q.1 * b q.2 - a q.2 * b q.1)) := by
    funext q
    rw [map_sub (IntermediateField.inclusion h), map_mul (IntermediateField.inclusion h),
      map_mul (IntermediateField.inclusion h)]
  show Real.log (⨆ i, ν' (IntermediateField.inclusion h (a i)))
      + Real.log (⨆ i, ν' (IntermediateField.inclusion h (b i)))
      - Real.log (⨆ q : ι × ι, ν' (IntermediateField.inclusion h (a q.1) * IntermediateField.inclusion h (b q.2)
          - IntermediateField.inclusion h (a q.2) * IntermediateField.inclusion h (b q.1)))
      = d * (Real.log (⨆ i, ν (a i)) + Real.log (⨆ i, ν (b i))
          - Real.log (⨆ q : ι × ι, ν (a q.1 * b q.2 - a q.2 * b q.1)))
  rw [show (⨆ q : ι × ι, ν' (IntermediateField.inclusion h (a q.1) * IntermediateField.inclusion h (b q.2)
          - IntermediateField.inclusion h (a q.2) * IntermediateField.inclusion h (b q.1)))
      = ⨆ q : ι × ι, ν' (IntermediateField.inclusion h (a q.1 * b q.2 - a q.2 * b q.1)) from congrArg iSup h3,
    log_iSup_inclusion h ν ν' hd hν' a, log_iSup_inclusion h ν ν' hd hν' b,
    log_iSup_inclusion h ν ν' hd hν' (fun q : ι × ι => a q.1 * b q.2 - a q.2 * b q.1)]
  ring

private theorem sum_prox_inclusion {ι : Type*} [Finite ι] {α : Type*} (D : α →₀ ℤ) (x : α → ι → ↥L) (a : ι → ↥L) :
    (D.sum fun w n => (n : ℝ) * prox ν' (fun i => IntermediateField.inclusion h (a i))
        (fun i => IntermediateField.inclusion h (x w i)))
      = d * D.sum fun w n => (n : ℝ) * prox ν a (x w) := by
  simp only [Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [prox_inclusion h ν ν' hd hν']; ring

end Transfer

private theorem regVal_zero_eq_secVal {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (v : Place (AlgebraicClosure ℚ) F) (t : F) (k : ℕ) (u : F) : regVal s v t k 0 u = secVal s v k u := by
  unfold regVal secVal
  simp only [pow_zero, mul_one]

private theorem coeffSum_eq_zero (N : ℕ) [NeZero N] (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hA : ∀ w, A w = w.ord f) :
    (A.sum fun _ n => n) = 0 := by
  haveI hpd : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, hdeg⟩ := hpd.exists_divisor f hf
  have hAD : A = D := Finsupp.ext fun w => by rw [hA w, hD w]
  have h1 : Divisor.degree A = A.sum fun v n => n * (v.deg : ℤ) := rfl
  have h2 : (A.sum fun v n => n * (v.deg : ℤ)) = A.sum fun _ n => n := by
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ModularCurve.deg_eq_one_modularFunctionFieldBar N w]
    simp
  rw [← h2, ← h1, hAD]
  exact hdeg

private theorem sum_divisor_of_section (N : ℕ) [NeZero N] (k : ℕ)
    (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    (B.sum fun _ m => m) = (k : ℤ) * ((embDivisor N).sum fun _ m => m) := by
  haveI hpd : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, _⟩ := hpd.exists_divisor u hu
  have hBD : B = D + (k : ℤ) • embDivisor N := Finsupp.ext fun w => by
    rw [Finsupp.add_apply, hD w, hB w]
  have hsum0 : (D.sum fun _ m => m) = 0 := coeffSum_eq_zero N u hu D hD
  rw [hBD, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    hsum0, zero_add,
    Finsupp.sum_smul_index' (fun _ => rfl)]
  simp only [smul_eq_mul, Finsupp.sum, Finset.mul_sum]

private theorem coeff_nonneg_and_le (N : ℕ) [NeZero N] (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (hmem : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ ((B w₀ : ℤ) : ℝ) ∧
      ((B w₀ : ℤ) : ℝ) ≤ (k : ℝ) * ((((embDivisor N).sum fun _ m => m : ℤ) : ℝ)) := by
  have hBeff : ∀ w, 0 ≤ B w := fun w => by
    have hord := (mem_riemannRochSpace_iff.mp hmem w).resolve_left hu
    rw [hB w]
    linarith [hord]
  have hZ := sum_divisor_of_section N k u hu B hB
  have hle : B w₀ ≤ B.sum fun _ m => m := by
    by_cases h0 : B w₀ = 0
    · rw [h0]
      simp only [Finsupp.sum]
      exact Finset.sum_nonneg fun i _ => hBeff i
    · simp only [Finsupp.sum]
      exact Finset.single_le_sum (fun i _ => hBeff i) (Finsupp.mem_support_iff.mpr h0)
  refine ⟨by exact_mod_cast hBeff w₀, ?_⟩
  calc ((B w₀ : ℤ) : ℝ) ≤ ((B.sum fun _ m => m : ℤ) : ℝ) := by exact_mod_cast hle
    _ = (k : ℝ) * ((((embDivisor N).sum fun _ m => m : ℤ) : ℝ)) := by rw [hZ]; push_cast; ring

end ModularCurve.JZero.BadPrimes

open ModularCurve.JZero.BadPrimes in

theorem solution (N : ℕ) [NeZero N]
    (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (t : modularFunctionFieldBar N) (ht : (cuspInftyBar N).ord t = 1) (S₀ : Finset ℕ)
    (hS₀ : ∀ p ∈ S₀, p.Prime) :
    ∃ c : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L) (p : ℕ), p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x (cuspInftyBar N) i : ↥L) : AlgebraicClosure ℚ) = evalVec s (cuspInftyBar N) i) →
      ∀ c' : ↥L, (c' : AlgebraicClosure ℚ) = regVal s (cuspInftyBar N) t k (B (cuspInftyBar N)).toNat u →
      ∃ m : ℝ,
        |((B.erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * prox ν (x (cuspInftyBar N)) (x w))
            - ((k : ℝ) * Real.log (⨆ i, ν (x (cuspInftyBar N) i)) - Real.log (ν c') - m)|
          ≤ c * k * (-Real.log (ν (p : ↥L))) ∧
        ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), B v = 0 →
          (∀ i, ((x v i : ↥L) : AlgebraicClosure ℚ) = evalVec s v i) →
          ∀ a : ↥L, (a : AlgebraicClosure ℚ) = secVal s v k u →
          |(B.sum fun w n => (n : ℝ) * prox ν (x v) (x w))
              - ((k : ℝ) * Real.log (⨆ i, ν (x v i)) - Real.log (ν a) - m)|
            ≤ c * k * (-Real.log (ν (p : ↥L))) := by
  classical
  obtain ⟨c₀, hn3⟩ := ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le N hN hN5 s hs S₀

  set o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := cuspInftyBar N with ho
  set Y : Fin r × Fin r → AlgebraicClosure ℚ := fun q =>
    regVal s o t 1 1 (evalVec s o q.1 • s q.2 - evalVec s o q.2 • s q.1) with hY
  choose Cx hCx using fun i : Fin r =>
    NumberField.FinitePlace.exists_abs_log_le_mul_neg_log_of_coe_eq (evalVec s o i)
  choose Cy hCy using fun q : Fin r × Fin r =>
    NumberField.FinitePlace.exists_abs_log_le_mul_neg_log_of_coe_eq (Y q)
  set M : ℝ := ((((embDivisor N).sum fun _ m => m : ℤ) : ℝ)) with hM
  refine ⟨max c₀ 0 + |M| * (2 * ∑ i, Cx i + ∑ q, Cy q), ?_⟩
  intro k u hu huR B hB L _ ν p hpS hνp x hx hxo c' hc'
  have hp : p.Prime := hS₀ p hpS
  have hP : 0 ≤ -Real.log (ν (p : ↥L)) := by
    have := Real.log_nonpos (apply_nonneg ν _) hνp.le
    linarith
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k

  haveI hfdY : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ (Set.range Y)) :=
    finiteDimensional_adjoin_range Y
  set L' : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ (Set.range Y) with hL'
  haveI hfd : FiniteDimensional ℚ ↥L' := IntermediateField.finiteDimensional_sup L _
  haveI : NumberField ↥L' := numberField_of_finiteDimensional L'
  have hLL' : L ≤ L' := le_sup_left
  obtain ⟨ν', d, hd, hν'⟩ := NumberField.FinitePlace.exists_finitePlace_inclusion_eq_rpow hLL' ν
  have hYmem : ∀ q, Y q ∈ L' := fun q =>
    (le_sup_right : IntermediateField.adjoin ℚ (Set.range Y) ≤ L')
      (IntermediateField.subset_adjoin ℚ (Set.range Y) ⟨q, rfl⟩)

  have hpL' : ((p : ℕ) : ↥L') = IntermediateField.inclusion hLL' (p : ↥L) :=
    (map_natCast (IntermediateField.inclusion hLL') p).symm
  have hνp' : ν' (p : ↥L') < 1 := by
    rw [hpL', hν']
    exact Real.rpow_lt_one (apply_nonneg ν _) hνp hd
  have hlogP : -Real.log (ν' (p : ↥L')) = d * (-Real.log (ν (p : ↥L))) := by
    rw [hpL', log_inclusion hLL' ν ν' hd hν']
    ring

  have hxB : ∀ w ∈ B.support, ∀ i,
      ((IntermediateField.inclusion hLL' (x w i) : ↥L') : AlgebraicClosure ℚ) = evalVec s w i :=
    fun w hw i => by rw [IntermediateField.coe_inclusion]; exact hx w hw i
  obtain ⟨m, hm⟩ := hn3 k u hu huR B hB L' ν' p hp hpS hνp'
    (fun w i => IntermediateField.inclusion hLL' (x w i)) hxB
  refine ⟨m / d, ?_, ?_⟩
  ·
    have hxo' : ∀ i, ((IntermediateField.inclusion hLL' (x o i) : ↥L') : AlgebraicClosure ℚ) = evalVec s o i :=
      fun i => by rw [IntermediateField.coe_inclusion]; exact hxo i
    have hc'' : ((IntermediateField.inclusion hLL' c' : ↥L') : AlgebraicClosure ℚ)
        = regVal s o t k (B o).toNat u := by
      rw [IntermediateField.coe_inclusion]; exact hc'
    let y : Fin r × Fin r → ↥L' := fun q => ⟨Y q, hYmem q⟩
    have hy : 0 < B o → ∀ q, ((y q : ↥L') : AlgebraicClosure ℚ)
        = regVal s o t 1 1 (evalVec s o q.1 • s q.2 - evalVec s o q.2 • s q.1) := fun _ _ => rfl
    have hy' : 0 < B o → (⨆ q, ν' (y q)) ≠ 0 := fun _ => by
      obtain ⟨q₀, hq₀⟩ := ModularCurve.JZero.exists_regVal_chord_ne_zero N s hs o t ht
      have hyq : y q₀ ≠ 0 := fun h0 => hq₀ (by
        have := congrArg (fun z : ↥L' => (z : AlgebraicClosure ℚ)) h0
        simpa [y] using this)
      exact ((NumberField.FinitePlace.pos_iff.mpr hyq).trans_le
        (le_ciSup (Set.finite_range fun q => ν' (y q)).bddAbove q₀)).ne'
    have key := hm o t (fun _ => ht) hxo' (IntermediateField.inclusion hLL' c') hc'' y hy hy'
    obtain ⟨hβ, hβk⟩ := coeff_nonneg_and_le N k u hu huR B hB o
    have hβk' : ((B o : ℤ) : ℝ) ≤ (k : ℝ) * |M| := hβk.trans (mul_le_mul_of_nonneg_left (le_abs_self M) hk)
    have hXabs : |Real.log (⨆ i, ν (x o i))| ≤ (∑ i, Cx i) * (-Real.log (ν (p : ↥L))) :=
      abs_log_iSup_le ν (x o) Cx (fun i => (hCx i).1) hP
        (fun i => (hCx i).2 L ν p hp hνp (x o i) (hxo i))
    have hYabs : |Real.log (⨆ q, ν' (y q))| ≤ (∑ q, Cy q) * (-Real.log (ν' (p : ↥L'))) :=
      abs_log_iSup_le ν' y Cy (fun q => (hCy q).1) (by rw [hlogP]; positivity)
        (fun q => (hCy q).2 L' ν' p hp hνp' (y q) rfl)
    exact assemble_cusp hd hP hk hβ hβk' (Finset.sum_nonneg fun i _ => (hCx i).1)
      (Finset.sum_nonneg fun q _ => (hCy q).1)
      (sum_prox_inclusion hLL' ν ν' hd hν' (B.erase o) x (x o))
      (log_iSup_inclusion hLL' ν ν' hd hν' (x o))
      (log_inclusion hLL' ν ν' hd hν' c') hlogP key hXabs hYabs
  ·
    intro v hv hxv a ha
    have hBv : ¬ (0 < B v) := by rw [hv]; exact lt_irrefl 0
    have hxv' : ∀ i, ((IntermediateField.inclusion hLL' (x v i) : ↥L') : AlgebraicClosure ℚ) = evalVec s v i :=
      fun i => by rw [IntermediateField.coe_inclusion]; exact hxv i
    have ha' : ((IntermediateField.inclusion hLL' a : ↥L') : AlgebraicClosure ℚ)
        = regVal s v t k (B v).toNat u := by
      rw [IntermediateField.coe_inclusion, ha, hv, Int.toNat_zero, regVal_zero_eq_secVal]
    have key := hm v t (fun h0 => absurd h0 hBv) hxv' (IntermediateField.inclusion hLL' a) ha'
      (fun _ => 0) (fun h0 => absurd h0 hBv) (fun h0 => absurd h0 hBv)
    have herase : B.erase v = B := Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr hv)
    have hS : ((B.erase v).sum fun w n => (n : ℝ) * prox ν' (fun i => IntermediateField.inclusion hLL' (x v i))
          (fun i => IntermediateField.inclusion hLL' (x w i)))
        = d * B.sum fun w n => (n : ℝ) * prox ν (x v) (x w) := by
      rw [sum_prox_inclusion hLL' ν ν' hd hν' (B.erase v) x (x v), herase]
    have hc0 : c₀ ≤ max c₀ 0 + |M| * (2 * ∑ i, Cx i + ∑ q, Cy q) := by
      have h1 : 0 ≤ ∑ i, Cx i := Finset.sum_nonneg fun i _ => (hCx i).1
      have h2 : 0 ≤ ∑ q, Cy q := Finset.sum_nonneg fun q _ => (hCy q).1
      have h3 : 0 ≤ |M| * (2 * ∑ i, Cx i + ∑ q, Cy q) := mul_nonneg (abs_nonneg M) (by linarith)
      linarith [le_max_left c₀ 0]
    exact assemble_off hd hP hk hc0 (by rw [hv, Int.cast_zero]) hS
      (log_iSup_inclusion hLL' ν ν' hd hν' (x v)) (log_inclusion hLL' ν ν' hd hν' a) hlogP key

end S_ModularCurve_JZero_jensen_bad_primes_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_bad_primes_of_prime_of_five_le (solution)
