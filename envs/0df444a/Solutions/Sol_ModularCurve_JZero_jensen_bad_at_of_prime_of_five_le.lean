-- Prove2me | solution 1 for ModularCurve.JZero.jensen_bad_at_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9dda9800-923e-5e9e-9ad0-70fef93a79ca

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_exists_greenKernel_regularizedAt_of_prime_of_five_le
import Theorems.Thm_NumberField_exists_isNonarchimedean_absoluteValue_extends
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_bad_at_of_prime_of_five_le
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
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

noncomputable section

namespace P2MW

section Eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem evalAt_zero (Q : Place K F) : Q.evalAt (0 : F) = 0 := by
  have h := Q.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

private theorem ord_nonneg_of_mem (Q : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ Q.toValuationSubring) :
    0 ≤ Q.ord f := by
  have h1 : Q.adicValuation f ≤ 1 := by
    have := Q.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : Q.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := Q.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (Q.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (Q.adicValuation f))
  omega

private theorem mem_of_eq_zero_or_ord_nonneg (Q : Place K F) {f : F} (h : f = 0 ∨ 0 ≤ Q.ord f) :
    f ∈ Q.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 (h.resolve_left hf0)

private theorem ord_eq_zero_of_evalAt_ne_zero (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f ≠ 0) : Q.ord f = 0 := by
  have hres : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply Q.algebraMap_residueField_injective
    rw [Q.algebraMap_evalAt hQ hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := Q.ord_coe_unit u
  rwa [hu] at this

private theorem ne_zero_of_evalAt_ne_zero (Q : Place K F) {f : F} (h : Q.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact h (evalAt_zero Q)

private theorem evalAt_eq_zero_of_ord_pos (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) : Q.evalAt f = 0 := by
  by_contra hne
  have := ord_eq_zero_of_evalAt_ne_zero Q hQ hf hne
  omega

private theorem ord_pos_of_evalAt_eq_zero (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f = 0) : 0 < Q.ord f := by
  rcases (ord_nonneg_of_mem Q hf0 hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (Q.evalAt_ne_zero_of_ord_eq_zero hQ hf0 heq.symm)

private theorem evalAt_add_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f + g) = Q.evalAt f + Q.evalAt g := by
  apply Q.algebraMap_residueField_injective
  rw [map_add, Q.algebraMap_evalAt hQ (add_mem hf hg), Q.algebraMap_evalAt hQ hf, Q.algebraMap_evalAt hQ hg,
    ← map_add]
  rfl

private theorem evalAt_neg_of_mem (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf : f ∈ Q.toValuationSubring) :
    Q.evalAt (-f) = -Q.evalAt f := by
  apply Q.algebraMap_residueField_injective
  rw [map_neg, Q.algebraMap_evalAt hQ (neg_mem hf), Q.algebraMap_evalAt hQ hf, ← map_neg]
  rfl

private theorem evalAt_sub_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f - g) = Q.evalAt f - Q.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem Q hQ hf (neg_mem hg), evalAt_neg_of_mem Q hQ hg, ← sub_eq_add_neg]

private theorem smul_mem_of_mem (Q : Place K F) (a : K) {f : F} (hf : f ∈ Q.toValuationSubring) :
    a • f ∈ Q.toValuationSubring := by
  rw [Algebra.smul_def]; exact mul_mem (Q.algebraMap_mem' a) hf

private theorem evalAt_smul_of_mem (Q : Place K F) (hQ : Q.IsRational) (a : K) {f : F}
    (hf : f ∈ Q.toValuationSubring) : Q.evalAt (a • f) = a * Q.evalAt f := by
  rw [Algebra.smul_def, Q.evalAt_mul_of_mem hQ (Q.algebraMap_mem' a) hf, Q.evalAt_algebraMap_eq]

private theorem evalAt_sum_smul_of_mem {ι : Type*} (S : Finset ι) (Q : Place K F) (hQ : Q.IsRational)
    (c : ι → K) {f : ι → F} (hf : ∀ i, f i ∈ Q.toValuationSubring) :
    Q.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * Q.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact evalAt_zero Q
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem Q hQ (smul_mem_of_mem Q _ (hf a)) (sum_mem fun i _ => smul_mem_of_mem Q _ (hf i)),
      evalAt_smul_of_mem Q hQ _ (hf a), ih]

private theorem inv_mem_of_ord_eq_zero (Q : Place K F) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    f⁻¹ ∈ Q.toValuationSubring :=
  Q.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf0) (by rw [Q.ord_inv, h, neg_zero])

private theorem evalAt_mul_evalAt_inv (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    Q.evalAt f * Q.evalAt f⁻¹ = 1 := by
  rw [← Q.evalAt_mul_of_mem hQ (Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.ge) (inv_mem_of_ord_eq_zero Q hf0 h),
    mul_inv_cancel₀ hf0, Q.evalAt_one]

private theorem exists_ord_eq_one (Q : Place K F) : ∃ t : F, Q.ord t = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  exact ⟨(π : F), Q.ord_coe_irreducible hπ⟩

end Eval

end P2MW

end

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MJB

section Prox

private theorem abv_sub_le_max {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (a b : K) : μ (a - b) ≤ max (μ a) (μ b) := by
  have h := hμ a (-b)
  rw [← sub_eq_add_neg, μ.map_neg] at h
  exact h

private theorem prox_eq_zero_of_coord_eq_zero {K : Type*} [Field K] {r : ℕ} (μ : AbsoluteValue K ℝ)
    (hμ : IsNonarchimedean μ) (x y : Fin r → K) (i : Fin r) (hyi : y i = 0)
    (hxi : ∀ j, μ (x j) ≤ μ (x i)) (hx0 : 0 < μ (x i))
    (b : Fin r) (hyb : ∀ j, μ (y j) ≤ μ (y b)) (hy0 : 0 < μ (y b)) : prox μ x y = 0 := by
  haveI : Nonempty (Fin r) := ⟨i⟩
  have hX : (⨆ j, μ (x j)) = μ (x i) :=
    le_antisymm (ciSup_le hxi) (le_ciSup (f := fun j => μ (x j)) (Set.finite_range _).bddAbove i)
  have hY : (⨆ j, μ (y j)) = μ (y b) :=
    le_antisymm (ciSup_le hyb) (le_ciSup (f := fun j => μ (y j)) (Set.finite_range _).bddAbove b)
  have hW : (⨆ q : Fin r × Fin r, μ (x q.1 * y q.2 - x q.2 * y q.1)) = μ (x i) * μ (y b) := by
    refine le_antisymm (ciSup_le fun q => ?_) ?_
    · refine (abv_sub_le_max μ hμ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        exact mul_le_mul (hxi q.1) (hyb q.2) (apply_nonneg _ _) hx0.le
      · rw [map_mul]
        exact mul_le_mul (hxi q.2) (hyb q.1) (apply_nonneg _ _) hx0.le
    · have h := le_ciSup (f := fun q : Fin r × Fin r => μ (x q.1 * y q.2 - x q.2 * y q.1))
        (Set.finite_range _).bddAbove (i, b)
      have hib : μ (x i * y b - x b * y i) = μ (x i) * μ (y b) := by
        rw [hyi, mul_zero, sub_zero, map_mul]
      rw [hib] at h
      exact h
  unfold prox
  rw [hX, hY, hW, Real.log_mul hx0.ne' hy0.ne']
  ring

private theorem prox_coe {r : ℕ} {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
    (ν : NumberField.FinitePlace ↥L) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (hμν : ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a)
    (x y : Fin r → ↥L) (X Y : Fin r → AlgebraicClosure ℚ)
    (hx : ∀ i, ((x i : ↥L) : AlgebraicClosure ℚ) = X i) (hy : ∀ i, ((y i : ↥L) : AlgebraicClosure ℚ) = Y i) :
    prox ν x y = prox μ X Y := by
  have h1 : ∀ i, ν (x i) = μ (X i) := fun i => by rw [← hμν, hx]
  have h2 : ∀ i, ν (y i) = μ (Y i) := fun i => by rw [← hμν, hy]
  have h3 : ∀ q : Fin r × Fin r, ν (x q.1 * y q.2 - x q.2 * y q.1) = μ (X q.1 * Y q.2 - X q.2 * Y q.1) := by
    intro q
    rw [← hμν]
    push_cast
    rw [hx, hx, hy, hy]
  unfold prox
  simp only [h1, h2, h3]

end Prox

section Pair

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

private def pair (D : Divisor (AlgebraicClosure ℚ) F) (G : Place (AlgebraicClosure ℚ) F → ℝ) : ℝ :=
  D.sum fun w n => (n : ℝ) * G w

private theorem pair_def (D : Divisor (AlgebraicClosure ℚ) F) (G : Place (AlgebraicClosure ℚ) F → ℝ) :
    pair D G = D.sum fun w n => (n : ℝ) * G w := rfl

private theorem pair_add (D₁ D₂ : Divisor (AlgebraicClosure ℚ) F) (G : Place (AlgebraicClosure ℚ) F → ℝ) :
    pair (D₁ + D₂) G = pair D₁ G + pair D₂ G := by
  unfold pair
  rw [Finsupp.sum_add_index' (fun w => by simp) (fun w m₁ m₂ => by push_cast; ring)]

private theorem pair_zsmul (k : ℤ) (D : Divisor (AlgebraicClosure ℚ) F) (G : Place (AlgebraicClosure ℚ) F → ℝ) :
    pair (k • D) G = (k : ℝ) * pair D G := by
  unfold pair
  rw [Finsupp.sum_smul_index' (fun w => by simp), Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [smul_eq_mul, zsmul_eq_mul]
  push_cast; ring

private theorem pair_neg (D : Divisor (AlgebraicClosure ℚ) F) (G : Place (AlgebraicClosure ℚ) F → ℝ) :
    pair (-D) G = -pair D G := by
  rw [← neg_one_zsmul, pair_zsmul]; push_cast; ring

private theorem pair_sub (D₁ D₂ : Divisor (AlgebraicClosure ℚ) F) (G : Place (AlgebraicClosure ℚ) F → ℝ) :
    pair (D₁ - D₂) G = pair D₁ G - pair D₂ G := by
  rw [sub_eq_add_neg, pair_add, pair_neg, ← sub_eq_add_neg]

private theorem abs_pair_le (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ w, 0 ≤ D w) (G : Place (AlgebraicClosure ℚ) F → ℝ)
    (M : ℝ) (hG : ∀ w, 0 < D w → |G w| ≤ M) :
    |pair D G| ≤ M * D.sum (fun _ n => (n : ℝ)) := by
  classical
  unfold pair
  simp only [Finsupp.sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w hw => ?_)
  have hpos : 0 < D w := lt_of_le_of_ne (hD w) (Ne.symm (Finsupp.mem_support_iff.mp hw))
  rw [abs_mul, abs_of_nonneg (by exact_mod_cast (hD w) : (0 : ℝ) ≤ (D w : ℝ))]
  have := hG w hpos
  have h0 : (0 : ℝ) ≤ (D w : ℝ) := by exact_mod_cast hD w
  nlinarith [abs_nonneg (G w)]

end Pair

section Bar

variable (N : ℕ) [NeZero N]

private theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

variable {N}

private theorem exists_forall_ord_le {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

private theorem ord_pivot_le {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

private theorem evalVec_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]; simp only [dif_pos hr]

private theorem secVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (k : ℕ) (u : modularFunctionFieldBar N) :
    secVal s v k u = v.evalAt (u * ((s (pivotIndex s v hr))⁻¹) ^ k) := by
  rw [secVal]; simp only [dif_pos hr]

private theorem regVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (k e : ℕ)
    (u : modularFunctionFieldBar N) :
    regVal s o t k e u = o.evalAt (u * ((s (pivotIndex s o hr))⁻¹) ^ k * (t⁻¹) ^ e) := by
  rw [regVal]; simp only [dif_pos hr]

private theorem effective_of_mem {k : ℕ} {u : modularFunctionFieldBar N} (hu0 : u ≠ 0)
    (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    ∀ w, 0 ≤ B w := by
  intro w
  rw [hB w]
  have := ((mem_riemannRochSpace_iff.mp hu) w).resolve_left hu0
  linarith

private theorem degree_eq_sum_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (D.degree : ℝ) = D.sum (fun _ n => (n : ℝ)) := by
  classical
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [deg_eq_one_modularFunctionFieldBar N w]

private theorem mass_eq {k : ℕ} {u : modularFunctionFieldBar N} (hu0 : u ≠ 0)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (Du : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hDu : ∀ w, Du w = w.ord u) (hDudeg : Du.degree = 0) :
    B.sum (fun _ n => (n : ℝ)) = (k : ℝ) * embDegree N := by
  have hBeq : B = Du + (k : ℤ) • embDivisor N := by
    ext w; rw [hB w, Finsupp.add_apply, hDu w]
  rw [← degree_eq_sum_bar, hBeq, map_add, map_zsmul, hDudeg, zero_add, embDivisor, map_zsmul, Divisor.degree_single,
    deg_eq_one_modularFunctionFieldBar N]
  simp only [smul_eq_mul, zsmul_eq_mul]
  push_cast; ring

end Bar

section PointLine

variable (N : ℕ) [NeZero N]

private theorem pointLine {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
    (c : modularFunctionFieldBar N → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hmult : ∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂)
    (hgreen : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
      ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
        (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f)
    (hbound : ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
      |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ lam)
    (hconst : ∀ i : Fin r, |c (s i)| ≤ lam)
    (k : ℕ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0) (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hBP : B P = 0) :
    |(B.sum fun w n => (n : ℝ) * prox μ (evalVec s P) (evalVec s w))
        - ((k : ℝ) * Real.log (⨆ i, μ (evalVec s P i)) - Real.log (μ (secVal s P k u)) + c u)|
      ≤ (2 * (embDegree N : ℝ) + 1) * k * lam := by
  classical
  have HPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsE : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  have hbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i : Fin r, w.ord (s i) + embDivisor N w = 0 :=
    fun w => exists_ord_add_embDivisor_eq_zero N s hs w
  obtain ⟨i₀, -⟩ := hbpf P
  have hr : 0 < r := i₀.pos
  haveI : Nonempty (Fin r) := ⟨i₀⟩
  have hPr := isRational_bar N P

  have hc1 : c 1 = 0 := by
    have h := hmult 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h; linarith
  have hcinv : ∀ f : modularFunctionFieldBar N, f ≠ 0 → c f⁻¹ = -c f := by
    intro f hf
    have h := hmult f f⁻¹ hf (inv_ne_zero hf)
    rw [mul_inv_cancel₀ hf, hc1] at h; linarith
  have hcpow : ∀ f : modularFunctionFieldBar N, f ≠ 0 → ∀ n : ℕ, c (f ^ n) = (n : ℝ) * c f := by
    intro f hf n
    induction n with
    | zero => rw [pow_zero, hc1, Nat.cast_zero, zero_mul]
    | succ n ih => rw [pow_succ, hmult _ _ (pow_ne_zero n hf) hf, ih]; push_cast; ring

  choose Hd hHd hHdeg using fun i => HPD.exists_divisor (s i) (hs0 i)
  let H : Fin r → Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := fun i => Hd i + embDivisor N
  have hH : ∀ i w, H i w = w.ord (s i) + embDivisor N w := fun i w => by
    show (Hd i + embDivisor N) w = _; rw [Finsupp.add_apply, hHd i w]
  have hH1 : ∀ i w, H i w = w.ord (s i) + (((1 : ℕ) : ℤ) • embDivisor N) w := fun i w => by
    rw [hH, Nat.cast_one, one_smul]
  have hsE1 : ∀ i, s i ∈ riemannRochSpace (((1 : ℕ) : ℤ) • embDivisor N) := fun i => by
    rw [Nat.cast_one, one_smul]; exact hsE i
  have hHnn : ∀ i w, 0 ≤ H i w := fun i => effective_of_mem (hs0 i) (hsE1 i) (H i) (hH1 i)
  have hHmass : ∀ i, (H i).sum (fun _ n => (n : ℝ)) = embDegree N := fun i => by
    have := mass_eq (hs0 i) (H i) (hH1 i) (Hd i) (hHd i) (hHdeg i)
    rw [this]; push_cast; ring

  set piv := pivotIndex s P hr with hpiv_def
  have hpiv : ∀ j, P.ord (s piv) ≤ P.ord (s j) := ord_pivot_le hr s P
  have hHpiv : H piv P = 0 := by
    obtain ⟨i, hi⟩ := hbpf P
    have h1 := hpiv i
    have h2 := hHnn piv P
    rw [hH] at h2 ⊢
    omega

  set Y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → AlgebraicClosure ℚ := evalVec s with hY_def
  have hY : ∀ w i, Y w i = w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) := fun w i => evalVec_apply hr s w i
  have hord_ratio : ∀ w i j, w.ord (s i * (s j)⁻¹) = H i w - H j w := fun w i j => by
    rw [Place.ord_mul _ (hs0 i) (inv_ne_zero (hs0 j)), Place.ord_inv, hH, hH]; ring
  have hHpivw : ∀ w, H (pivotIndex s w hr) w = 0 := by
    intro w
    obtain ⟨i, hi⟩ := hbpf w
    have h1 := ord_pivot_le hr s w i
    have h2 := hHnn (pivotIndex s w hr) w
    rw [hH] at h2 ⊢
    omega
  have hratmem : ∀ w i, s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring := fun w i =>
    w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 _)))
      (by rw [hord_ratio, hHpivw, sub_zero]; exact hHnn i w)
  have hYpiv : ∀ w, Y w (pivotIndex s w hr) = 1 := fun w => by
    rw [hY, mul_inv_cancel₀ (hs0 _), Place.evalAt_one]
  have hYzero : ∀ w i, 0 < H i w → Y w i = 0 := by
    intro w i hpos
    rw [hY]
    have hne : s i * (s (pivotIndex s w hr))⁻¹ ≠ 0 := mul_ne_zero (hs0 i) (inv_ne_zero (hs0 _))
    have hord : 0 < w.ord (s i * (s (pivotIndex s w hr))⁻¹) := by rw [hord_ratio, hHpivw]; omega
    exact P2MW.evalAt_eq_zero_of_ord_pos w (isRational_bar N w) (hratmem w i) hord

  set S : ℝ := ⨆ i, μ (Y P i) with hS
  have hSge : ∀ i, μ (Y P i) ≤ S := fun i => by
    rw [hS]; exact le_ciSup (f := fun i => μ (Y P i)) (Set.finite_range _).bddAbove i
  have hS1 : 1 ≤ S := by have h := hSge piv; rwa [hYpiv, map_one] at h
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS1
  obtain ⟨istar, histar⟩ : ∃ i, μ (Y P i) = S := by rw [hS]; exact exists_eq_ciSup_of_finite
  have hYstar0 : Y P istar ≠ 0 := by
    intro h0; rw [h0, map_zero] at histar; linarith
  have hHstar : H istar P = 0 := by
    rcases (hHnn istar P).lt_or_eq with hpos | h0
    · exact absurd (hYzero P istar hpos) hYstar0
    · exact h0.symm

  have hsmall : ∀ w, 0 < H istar w → |g P w| ≤ lam := by
    intro w hpos
    have hPw : P ≠ w := by intro h; rw [← h] at hpos; omega
    have hb := hbound P w hPw

    obtain ⟨b, hb'⟩ : ∃ b, μ (Y w b) = ⨆ j, μ (Y w j) := exists_eq_ciSup_of_finite
    have hwge : ∀ j, μ (Y w j) ≤ μ (Y w b) := fun j => by
      rw [hb']; exact le_ciSup (f := fun j => μ (Y w j)) (Set.finite_range _).bddAbove j
    have hwpos : 0 < μ (Y w b) := by
      have := hwge (pivotIndex s w hr); rw [hYpiv, map_one] at this; linarith
    have hprox0 : prox μ (Y P) (Y w) = 0 :=
      prox_eq_zero_of_coord_eq_zero μ hμ (Y P) (Y w) istar (hYzero w istar hpos)
        (fun j => by rw [histar]; exact hSge j) (by rw [histar]; exact hSpos) b hwge hwpos
    rw [hY_def] at hprox0
    rw [hprox0, sub_zero] at hb
    exact hb
  have hbeta : |pair (H istar) (g P)| ≤ lam * embDegree N := by
    have := abs_pair_le (H istar) (hHnn istar) (g P) lam hsmall
    rwa [hHmass] at this

  have hφ0 : u * ((s piv)⁻¹) ^ k ≠ 0 := mul_ne_zero hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv)))
  have hdivφ : ∀ w, (B - (k : ℤ) • H piv) w = w.ord (u * ((s piv)⁻¹) ^ k) := by
    intro w
    rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hB w, hH, Place.ord_mul _ hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv))),
      ← zpow_natCast, Place.ord_zpow, Place.ord_inv, Finsupp.smul_apply, smul_eq_mul]
    ring
  have hG1 := hgreen _ hφ0 (B - (k : ℤ) • H piv) hdivφ P (by rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hBP, hHpiv, mul_zero, sub_zero])
  have hcφ : c (u * ((s piv)⁻¹) ^ k) = c u - (k : ℝ) * c (s piv) := by
    rw [hmult _ _ hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv))), hcpow _ (inv_ne_zero (hs0 piv)), hcinv _ (hs0 piv)]; ring
  have hφval : P.evalAt (u * ((s piv)⁻¹) ^ k) = secVal s P k u := by rw [secVal_apply hr s P k u]

  have hψ0 : s piv * (s istar)⁻¹ ≠ 0 := mul_ne_zero (hs0 piv) (inv_ne_zero (hs0 istar))
  have hdivψ : ∀ w, (H piv - H istar) w = w.ord (s piv * (s istar)⁻¹) := by
    intro w; rw [Finsupp.sub_apply, hord_ratio]
  have hG2 := hgreen _ hψ0 (H piv - H istar) hdivψ P (by rw [Finsupp.sub_apply, hHpiv, hHstar, sub_zero])
  have hcψ : c (s piv * (s istar)⁻¹) = c (s piv) - c (s istar) := by
    rw [hmult _ _ (hs0 piv) (inv_ne_zero (hs0 istar)), hcinv _ (hs0 istar)]; ring
  have hψval : μ (P.evalAt (s piv * (s istar)⁻¹)) = S⁻¹ := by

    have hmem1 : s istar * (s piv)⁻¹ ∈ P.toValuationSubring := hratmem P istar
    have hord0 : P.ord (s istar * (s piv)⁻¹) = 0 := by rw [hord_ratio, hHstar, hHpiv, sub_zero]
    have hinv : (s istar * (s piv)⁻¹)⁻¹ = s piv * (s istar)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
    have h1 := P2MW.evalAt_mul_evalAt_inv P hPr (mul_ne_zero (hs0 istar) (inv_ne_zero (hs0 piv))) hord0
    rw [hinv, ← hY P istar] at h1
    have h2 : μ (Y P istar) * μ (P.evalAt (s piv * (s istar)⁻¹)) = 1 := by rw [← map_mul, h1, map_one]
    rw [histar] at h2
    exact eq_inv_of_mul_eq_one_right h2

  have hsumB : pair B (g P) = pair (B - (k : ℤ) • H piv) (g P) + (k : ℝ) * (pair (H piv - H istar) (g P) + pair (H istar) (g P)) := by
    rw [pair_sub, pair_zsmul, pair_sub]; push_cast; ring
  have e1 : pair (B - (k : ℤ) • H piv) (g P) = -Real.log (μ (secVal s P k u)) + (c u - (k : ℝ) * c (s piv)) := by
    rw [pair_def, hG1, hcφ, hφval]
  have e2 : pair (H piv - H istar) (g P) = Real.log S + (c (s piv) - c (s istar)) := by
    rw [pair_def, hG2, hcψ, hψval, Real.log_inv, neg_neg]

  have hBnn : ∀ w, 0 ≤ B w := effective_of_mem hu0 hu B hB
  obtain ⟨Du, hDu, hDudeg⟩ := HPD.exists_divisor u hu0
  have hBmass : B.sum (fun _ n => (n : ℝ)) = (k : ℝ) * embDegree N := mass_eq hu0 B hB Du hDu hDudeg
  have hdiff : |pair B (g P) - pair B (fun w => prox μ (Y P) (Y w))| ≤ lam * ((k : ℝ) * embDegree N) := by
    have hsub : pair B (g P) - pair B (fun w => prox μ (Y P) (Y w)) = pair B (fun w => g P w - prox μ (Y P) (Y w)) := by
      simp only [pair, Finsupp.sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => by ring
    rw [hsub, ← hBmass]
    refine abs_pair_le B hBnn _ lam fun w hw => ?_
    have hPw : P ≠ w := by intro h; rw [← h] at hw; omega
    have := hbound P w hPw
    rwa [hY_def]

  have hcs := hconst istar
  rw [abs_le] at hbeta hdiff hcs ⊢
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ embDegree N := Nat.cast_nonneg _
  show -((2 * (embDegree N : ℝ) + 1) * k * lam) ≤ pair B (fun w => prox μ (Y P) (Y w)) - ((k : ℝ) * Real.log S - Real.log (μ (secVal s P k u)) + c u)
    ∧ pair B (fun w => prox μ (Y P) (Y w)) - ((k : ℝ) * Real.log S - Real.log (μ (secVal s P k u)) + c u) ≤ (2 * (embDegree N : ℝ) + 1) * k * lam
  rw [hsumB, e1, e2] at hdiff
  constructor <;> nlinarith [hbeta.1, hbeta.2, hdiff.1, hdiff.2, hcs.1, hcs.2, hk0, hd0, hlam]

end PointLine

section GeneralLine

variable (N : ℕ) [NeZero N]

private theorem generalLine {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
    (c : modularFunctionFieldBar N → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hmult : ∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂)
    (hgreen : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
      ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
        (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f)
    (hbound : ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
      |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ lam)
    (hconst : ∀ i : Fin r, |c (s i)| ≤ lam)
    (k : ℕ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0) (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N)
    (ht : 0 < B P → P.ord t = 1) (lamR : ℝ) (hlamR : 0 ≤ lamR)
    (hreg : 0 < B P → ∀ Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, Dt w = w.ord t) →
      |((Dt.erase P).sum fun w n => (n : ℝ) * g P w) - c t
          - (Real.log (⨆ q : Fin r × Fin r, μ (regVal s P t 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
              - 2 * Real.log (⨆ i, μ (evalVec s P i)))| ≤ lamR) :
    |((B.erase P).sum fun w n => (n : ℝ) * prox μ (evalVec s P) (evalVec s w))
        - (((k : ℝ) - 2 * (B P : ℝ)) * Real.log (⨆ i, μ (evalVec s P i))
            + (B P : ℝ) * Real.log (⨆ q : Fin r × Fin r, μ (regVal s P t 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
            - Real.log (μ (regVal s P t k (B P).toNat u)) + c u)|
      ≤ (2 * (embDegree N : ℝ) + 1) * k * lam + (B P : ℝ) * lamR := by
  classical
  have HPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsE : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  have hbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i : Fin r, w.ord (s i) + embDivisor N w = 0 :=
    fun w => exists_ord_add_embDivisor_eq_zero N s hs w
  obtain ⟨i₀, -⟩ := hbpf P
  have hr : 0 < r := i₀.pos
  haveI : Nonempty (Fin r) := ⟨i₀⟩
  have hBnn : ∀ w, 0 ≤ B w := effective_of_mem hu0 hu B hB

  by_cases he : B P = 0
  · have hpt := pointLine N s hs μ hμ g c lam hlam hmult hgreen hbound hconst k u hu0 hu B hB P he
    have herase : B.erase P = B := by
      rw [Finsupp.erase_of_notMem_support]
      rwa [Finsupp.notMem_support_iff]
    have hreg0 : regVal s P t k (B P).toNat u = secVal s P k u := by
      rw [he, Int.toNat_zero, regVal, secVal]
      simp only [dif_pos hr, pow_zero, mul_one]
    rw [herase, hreg0, he]
    push_cast
    simp only [mul_zero, zero_mul, sub_zero, add_zero] at hpt ⊢
    exact hpt

  have hepos : 0 < B P := lt_of_le_of_ne (hBnn P) (Ne.symm he)
  have hordt : P.ord t = 1 := ht hepos
  have ht0 : t ≠ 0 := fun h => by rw [h, Place.ord_zero] at hordt; exact zero_ne_one hordt
  set e : ℕ := (B P).toNat with he_def
  have heZ : (e : ℤ) = B P := Int.toNat_of_nonneg (hBnn P)
  have heR : (e : ℝ) = (B P : ℝ) := by exact_mod_cast heZ
  have hPr := isRational_bar N P

  have hc1 : c 1 = 0 := by
    have h := hmult 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h; linarith
  have hcinv : ∀ f : modularFunctionFieldBar N, f ≠ 0 → c f⁻¹ = -c f := by
    intro f hf
    have h := hmult f f⁻¹ hf (inv_ne_zero hf)
    rw [mul_inv_cancel₀ hf, hc1] at h; linarith
  have hcpow : ∀ f : modularFunctionFieldBar N, f ≠ 0 → ∀ n : ℕ, c (f ^ n) = (n : ℝ) * c f := by
    intro f hf n
    induction n with
    | zero => rw [pow_zero, hc1, Nat.cast_zero, zero_mul]
    | succ n ih => rw [pow_succ, hmult _ _ (pow_ne_zero n hf) hf, ih]; push_cast; ring

  choose Hd hHd hHdeg using fun i => HPD.exists_divisor (s i) (hs0 i)
  let H : Fin r → Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := fun i => Hd i + embDivisor N
  have hH : ∀ i w, H i w = w.ord (s i) + embDivisor N w := fun i w => by
    show (Hd i + embDivisor N) w = _; rw [Finsupp.add_apply, hHd i w]
  have hH1 : ∀ i w, H i w = w.ord (s i) + (((1 : ℕ) : ℤ) • embDivisor N) w := fun i w => by
    rw [hH, Nat.cast_one, one_smul]
  have hsE1 : ∀ i, s i ∈ riemannRochSpace (((1 : ℕ) : ℤ) • embDivisor N) := fun i => by
    rw [Nat.cast_one, one_smul]; exact hsE i
  have hHnn : ∀ i w, 0 ≤ H i w := fun i => effective_of_mem (hs0 i) (hsE1 i) (H i) (hH1 i)
  have hHmass : ∀ i, (H i).sum (fun _ n => (n : ℝ)) = embDegree N := fun i => by
    have := mass_eq (hs0 i) (H i) (hH1 i) (Hd i) (hHd i) (hHdeg i)
    rw [this]; push_cast; ring

  set piv := pivotIndex s P hr with hpiv_def
  have hpiv : ∀ j, P.ord (s piv) ≤ P.ord (s j) := ord_pivot_le hr s P
  have hHpivw : ∀ w, H (pivotIndex s w hr) w = 0 := by
    intro w
    obtain ⟨i, hi⟩ := hbpf w
    have h1 := ord_pivot_le hr s w i
    have h2 := hHnn (pivotIndex s w hr) w
    rw [hH] at h2 ⊢
    omega
  have hHpiv : H piv P = 0 := hHpivw P
  set Y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → AlgebraicClosure ℚ := evalVec s with hY_def
  have hY : ∀ w i, Y w i = w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) := fun w i => evalVec_apply hr s w i
  have hord_ratio : ∀ w i j, w.ord (s i * (s j)⁻¹) = H i w - H j w := fun w i j => by
    rw [Place.ord_mul _ (hs0 i) (inv_ne_zero (hs0 j)), Place.ord_inv, hH, hH]; ring
  have hratmem : ∀ w i, s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring := fun w i =>
    w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 _)))
      (by rw [hord_ratio, hHpivw, sub_zero]; exact hHnn i w)
  have hYpiv : ∀ w, Y w (pivotIndex s w hr) = 1 := fun w => by
    rw [hY, mul_inv_cancel₀ (hs0 _), Place.evalAt_one]
  have hYzero : ∀ w i, 0 < H i w → Y w i = 0 := by
    intro w i hpos
    rw [hY]
    have hord : 0 < w.ord (s i * (s (pivotIndex s w hr))⁻¹) := by rw [hord_ratio, hHpivw]; omega
    exact P2MW.evalAt_eq_zero_of_ord_pos w (isRational_bar N w) (hratmem w i) hord

  set S : ℝ := ⨆ i, μ (Y P i) with hS
  have hSge : ∀ i, μ (Y P i) ≤ S := fun i => by
    rw [hS]; exact le_ciSup (f := fun i => μ (Y P i)) (Set.finite_range _).bddAbove i
  have hS1 : 1 ≤ S := by have h := hSge piv; rwa [hYpiv, map_one] at h
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS1
  obtain ⟨istar, histar⟩ : ∃ i, μ (Y P i) = S := by rw [hS]; exact exists_eq_ciSup_of_finite
  have hYstar0 : Y P istar ≠ 0 := by
    intro h0; rw [h0, map_zero] at histar; linarith
  have hHstar : H istar P = 0 := by
    rcases (hHnn istar P).lt_or_eq with hpos | h0
    · exact absurd (hYzero P istar hpos) hYstar0
    · exact h0.symm
  have hsmall : ∀ w, 0 < H istar w → |g P w| ≤ lam := by
    intro w hpos
    have hPw : P ≠ w := by intro h; rw [← h] at hpos; omega
    have hb := hbound P w hPw
    obtain ⟨b, hb'⟩ : ∃ b, μ (Y w b) = ⨆ j, μ (Y w j) := exists_eq_ciSup_of_finite
    have hwge : ∀ j, μ (Y w j) ≤ μ (Y w b) := fun j => by
      rw [hb']; exact le_ciSup (f := fun j => μ (Y w j)) (Set.finite_range _).bddAbove j
    have hwpos : 0 < μ (Y w b) := by
      have := hwge (pivotIndex s w hr); rw [hYpiv, map_one] at this; linarith
    have hprox0 : prox μ (Y P) (Y w) = 0 :=
      prox_eq_zero_of_coord_eq_zero μ hμ (Y P) (Y w) istar (hYzero w istar hpos)
        (fun j => by rw [histar]; exact hSge j) (by rw [histar]; exact hSpos) b hwge hwpos
    rw [hY_def] at hprox0
    rw [hprox0, sub_zero] at hb
    exact hb
  have hbeta : |pair (H istar) (g P)| ≤ lam * embDegree N := by
    have := abs_pair_le (H istar) (hHnn istar) (g P) lam hsmall
    rwa [hHmass] at this

  have hψ0 : s piv * (s istar)⁻¹ ≠ 0 := mul_ne_zero (hs0 piv) (inv_ne_zero (hs0 istar))
  have hdivψ : ∀ w, (H piv - H istar) w = w.ord (s piv * (s istar)⁻¹) := by
    intro w; rw [Finsupp.sub_apply, hord_ratio]
  have hG2 := hgreen _ hψ0 (H piv - H istar) hdivψ P (by rw [Finsupp.sub_apply, hHpiv, hHstar, sub_zero])
  have hcψ : c (s piv * (s istar)⁻¹) = c (s piv) - c (s istar) := by
    rw [hmult _ _ (hs0 piv) (inv_ne_zero (hs0 istar)), hcinv _ (hs0 istar)]; ring
  have hψval : μ (P.evalAt (s piv * (s istar)⁻¹)) = S⁻¹ := by
    have hord0 : P.ord (s istar * (s piv)⁻¹) = 0 := by rw [hord_ratio, hHstar, hHpiv, sub_zero]
    have hinv : (s istar * (s piv)⁻¹)⁻¹ = s piv * (s istar)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
    have h1 := P2MW.evalAt_mul_evalAt_inv P hPr (mul_ne_zero (hs0 istar) (inv_ne_zero (hs0 piv))) hord0
    rw [hinv, ← hY P istar] at h1
    have h2 : μ (Y P istar) * μ (P.evalAt (s piv * (s istar)⁻¹)) = 1 := by rw [← map_mul, h1, map_one]
    rw [histar] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have e2 : pair (H piv - H istar) (g P) = Real.log S + (c (s piv) - c (s istar)) := by
    rw [pair_def, hG2, hcψ, hψval, Real.log_inv, neg_neg]

  obtain ⟨Dt, hDt, -⟩ := HPD.exists_divisor t ht0
  have hDtP : Dt P = 1 := by rw [hDt, hordt]
  have hF0 : u * ((s piv)⁻¹) ^ k * (t⁻¹) ^ e ≠ 0 :=
    mul_ne_zero (mul_ne_zero hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv)))) (pow_ne_zero e (inv_ne_zero ht0))
  have hdivF : ∀ w, (B - (k : ℤ) • H piv - (e : ℤ) • Dt) w = w.ord (u * ((s piv)⁻¹) ^ k * (t⁻¹) ^ e) := by
    intro w
    rw [Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, hB w, hH, hDt,
      Place.ord_mul _ (mul_ne_zero hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv)))) (pow_ne_zero e (inv_ne_zero ht0)),
      Place.ord_mul _ hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv))),
      ← zpow_natCast, Place.ord_zpow, Place.ord_inv, ← zpow_natCast, Place.ord_zpow, Place.ord_inv,
      Finsupp.smul_apply, smul_eq_mul]
    ring
  have hG1 := hgreen _ hF0 (B - (k : ℤ) • H piv - (e : ℤ) • Dt) hdivF P (by
    rw [Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      hHpiv, hDtP, mul_zero, sub_zero, mul_one, ← heZ, sub_self])
  have hcF : c (u * ((s piv)⁻¹) ^ k * (t⁻¹) ^ e) = c u - (k : ℝ) * c (s piv) - (e : ℝ) * c t := by
    rw [hmult _ _ (mul_ne_zero hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv)))) (pow_ne_zero e (inv_ne_zero ht0)),
      hmult _ _ hu0 (pow_ne_zero k (inv_ne_zero (hs0 piv))), hcpow _ (inv_ne_zero (hs0 piv)), hcinv _ (hs0 piv),
      hcpow _ (inv_ne_zero ht0), hcinv _ ht0]; ring
  have hFval : P.evalAt (u * ((s piv)⁻¹) ^ k * (t⁻¹) ^ e) = regVal s P t k e u := by
    rw [regVal_apply hr s P t k e u]

  have hB_erase : pair B (g P) = ((B.erase P).sum fun w n => (n : ℝ) * g P w) + (B P : ℝ) * g P P := by
    have h := Finsupp.add_sum_erase' B P (fun w n => (n : ℝ) * g P w) (fun w => by simp)
    rw [pair_def]; linarith
  have hDt_erase : pair Dt (g P) = ((Dt.erase P).sum fun w n => (n : ℝ) * g P w) + g P P := by
    have h := Finsupp.add_sum_erase' Dt P (fun w n => (n : ℝ) * g P w) (fun w => by simp)
    rw [pair_def, hDtP] at *; push_cast at h; linarith
  have hsplit : pair (B - (k : ℤ) • H piv - (e : ℤ) • Dt) (g P)
      = pair B (g P) - (k : ℝ) * (pair (H piv - H istar) (g P) + pair (H istar) (g P)) - (e : ℝ) * pair Dt (g P) := by
    rw [pair_sub, pair_sub, pair_zsmul, pair_zsmul, pair_sub]; push_cast; ring
  have hR := hreg hepos Dt hDt

  obtain ⟨Du, hDu, hDudeg⟩ := HPD.exists_divisor u hu0
  have hBmass : B.sum (fun _ n => (n : ℝ)) = (k : ℝ) * embDegree N := mass_eq hu0 B hB Du hDu hDudeg
  have hEnn : ∀ w, 0 ≤ (B.erase P) w := by
    intro w; by_cases hw : w = P
    · rw [hw, Finsupp.erase_same]
    · rw [Finsupp.erase_ne hw]; exact hBnn w
  have hEmass : (B.erase P).sum (fun _ n => (n : ℝ)) ≤ (k : ℝ) * embDegree N := by
    have h := Finsupp.add_sum_erase' B P (fun _ n => (n : ℝ)) (fun w => by simp)
    rw [hBmass] at h
    have : (0 : ℝ) ≤ (B P : ℝ) := by exact_mod_cast hBnn P
    linarith
  have hdiff : |pair (B.erase P) (g P) - pair (B.erase P) (fun w => prox μ (Y P) (Y w))| ≤ lam * ((k : ℝ) * embDegree N) := by
    have hsub : pair (B.erase P) (g P) - pair (B.erase P) (fun w => prox μ (Y P) (Y w))
        = pair (B.erase P) (fun w => g P w - prox μ (Y P) (Y w)) := by
      simp only [pair, Finsupp.sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => by ring
    rw [hsub]
    refine (abs_pair_le (B.erase P) hEnn _ lam fun w hw => ?_).trans (mul_le_mul_of_nonneg_left hEmass hlam)
    have hPw : P ≠ w := by intro h; rw [← h, Finsupp.erase_same] at hw; exact lt_irrefl _ hw
    have := hbound P w hPw
    rwa [hY_def]

  have hcs := hconst istar
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ embDegree N := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ (B P : ℝ) := by exact_mod_cast hBnn P
  have main : ((B.erase P).sum fun w n => (n : ℝ) * g P w)
      = -Real.log (μ (regVal s P t k e u)) + c u + (k : ℝ) * Real.log S
        + (k : ℝ) * (pair (H istar) (g P) - c (s istar)) + (e : ℝ) * (((Dt.erase P).sum fun w n => (n : ℝ) * g P w) - c t) := by
    have h := hG1
    rw [← pair_def, hsplit, hcF, hFval, hB_erase, hDt_erase, e2] at h
    rw [heR] at h ⊢
    linarith
  rw [pair_def, pair_def] at hdiff
  rw [heR] at main
  rw [abs_le] at hbeta hdiff hcs hR ⊢
  rw [main] at hdiff
  constructor <;> nlinarith [hbeta.1, hbeta.2, hdiff.1, hdiff.2, hcs.1, hcs.2, hR.1, hR.2, hk0, hd0, hlam, he0, hlamR]

end GeneralLine

end P2MJB

end

namespace P2MJB

section ProxAlgebra

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ)

private theorem prox_comm {r : ℕ} (x y : Fin r → K) : prox μ x y = prox μ y x := by
  unfold prox
  have hW : (⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1))
      = ⨆ p : Fin r × Fin r, μ (y p.1 * x p.2 - y p.2 * x p.1) := by
    congr 1
    funext p
    rw [← μ.map_neg]
    congr 1
    ring
  rw [hW]
  ring

private theorem iSup_abv_mul {ι : Type*} (a : K) (x : ι → K) :
    (⨆ i, μ (a * x i)) = μ a * ⨆ i, μ (x i) := by
  rw [Real.mul_iSup_of_nonneg (apply_nonneg μ a)]
  congr 1
  funext i
  rw [map_mul]

private theorem iSup_wedge_smul_left {r : ℕ} (a : K) (x y : Fin r → K) :
    (⨆ p : Fin r × Fin r, μ ((a • x) p.1 * y p.2 - (a • x) p.2 * y p.1))
      = μ a * ⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1) := by
  rw [← iSup_abv_mul μ a]
  congr 1
  funext p
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem prox_smul_left {r : ℕ} (x y : Fin r → K) (a : K) (ha : a ≠ 0)
    (hW : (⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1)) ≠ 0) :
    prox μ (a • x) y = prox μ x y := by
  have hμa : 0 < μ a := μ.pos ha
  have hX : (⨆ i, μ ((a • x) i)) = μ a * ⨆ i, μ (x i) := by
    rw [← iSup_abv_mul μ a]
    congr 1

  have hX0 : (⨆ i, μ (x i)) ≠ 0 := by
    intro h0
    apply hW
    have hxi : ∀ i, x i = 0 := by
      intro i
      have hle : μ (x i) ≤ ⨆ i, μ (x i) := le_ciSup (f := fun i => μ (x i)) (Set.finite_range _).bddAbove i
      rw [h0] at hle
      exact (μ.eq_zero).mp (le_antisymm hle (apply_nonneg μ _))
    have : (fun p : Fin r × Fin r => μ (x p.1 * y p.2 - x p.2 * y p.1)) = fun _ => 0 := by
      funext p; rw [hxi, hxi, zero_mul, zero_mul, sub_zero, map_zero]
    rw [this]
    exact Real.iSup_const_zero
  unfold prox
  rw [hX, iSup_wedge_smul_left μ a x y, Real.log_mul hμa.ne' hX0, Real.log_mul hμa.ne' hW]
  ring

private theorem prox_smul_left_zero {r : ℕ} (y : Fin r → K) (a : K) :
    prox μ (a • (0 : Fin r → K)) y = prox μ (0 : Fin r → K) y := by
  rw [smul_zero]

private theorem prox_smul_right {r : ℕ} (x y : Fin r → K) (a : K) (ha : a ≠ 0)
    (hW : (⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1)) ≠ 0) :
    prox μ x (a • y) = prox μ x y := by
  rw [prox_comm μ x (a • y), prox_comm μ x y]
  apply prox_smul_left μ y x a ha

  have : (⨆ p : Fin r × Fin r, μ (y p.1 * x p.2 - y p.2 * x p.1))
      = ⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1) := by
    congr 1; funext p; rw [← μ.map_neg]; congr 1; ring
  rwa [this]

private theorem iSup_wedge_le (hμ : IsNonarchimedean μ) {r : ℕ} (x y : Fin r → K) :
    (⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1)) ≤ (⨆ i, μ (x i)) * ⨆ i, μ (y i) := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · haveI : IsEmpty (Fin r × Fin r) := by infer_instance
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, mul_zero]
  · have hx : ∀ i, μ (x i) ≤ ⨆ i, μ (x i) := fun i => le_ciSup (f := fun i => μ (x i)) (Set.finite_range _).bddAbove i
    have hy : ∀ i, μ (y i) ≤ ⨆ i, μ (y i) := fun i => le_ciSup (f := fun i => μ (y i)) (Set.finite_range _).bddAbove i
    have hX : 0 ≤ ⨆ i, μ (x i) := Real.iSup_nonneg fun i => apply_nonneg μ _
    refine ciSup_le fun p => ?_
    refine (abv_sub_le_max μ hμ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_mul (hx p.1) (hy p.2) (apply_nonneg μ _) hX
    · rw [map_mul]; exact mul_le_mul (hx p.2) (hy p.1) (apply_nonneg μ _) hX

private theorem prox_nonneg (hμ : IsNonarchimedean μ) {r : ℕ} (x y : Fin r → K)
    (hW : (⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1)) ≠ 0) : 0 ≤ prox μ x y := by
  have hWpos : 0 < ⨆ p : Fin r × Fin r, μ (x p.1 * y p.2 - x p.2 * y p.1) :=
    lt_of_le_of_ne (Real.iSup_nonneg fun p => apply_nonneg μ _) (Ne.symm hW)
  have hle := iSup_wedge_le μ hμ x y
  have hXpos : 0 < ⨆ i, μ (x i) := by
    rcases (Real.iSup_nonneg fun i => apply_nonneg μ (x i)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hle; exact absurd (hWpos.trans_le hle) (lt_irrefl 0)
  have hYpos : 0 < ⨆ i, μ (y i) := by
    rcases (Real.iSup_nonneg fun i => apply_nonneg μ (y i)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hle; exact absurd (hWpos.trans_le hle) (lt_irrefl 0)
  unfold prox
  have := Real.log_le_log hWpos hle
  rw [Real.log_mul hXpos.ne' hYpos.ne'] at this
  linarith

end ProxAlgebra

end P2MJB

namespace P2MJB

open ModularCurve

private theorem pointLine_nu (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
    (c : modularFunctionFieldBar N → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hmult : ∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂)
    (hgreen : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
      ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
        (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f)
    (hbound : ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
      |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ lam)
    (hconst : ∀ i : Fin r, |c (s i)| ≤ lam)
    (k : ℕ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0) (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : NumberField.FinitePlace ↥L)
    (hμν : ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a)
    (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L)
    (hx : ∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hBP : B P = 0)
    (hxP : ∀ i, ((x P i : ↥L) : AlgebraicClosure ℚ) = evalVec s P i)
    (a : ↥L) (ha : (a : AlgebraicClosure ℚ) = secVal s P k u) :
    |(B.sum fun w n => (n : ℝ) * prox ν (x P) (x w))
        - ((k : ℝ) * Real.log (⨆ i, ν (x P i)) - Real.log (ν a) + c u)|
      ≤ (2 * (embDegree N : ℝ) + 1) * k * lam := by
  classical
  have hmain := pointLine N s hs μ hμ g c lam hlam hmult hgreen hbound hconst k u hu0 hu B hB P hBP

  have hsum : (B.sum fun w n => (n : ℝ) * prox ν (x P) (x w))
      = B.sum fun w n => (n : ℝ) * prox μ (evalVec s P) (evalVec s w) := by
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun w hw => ?_
    show (B w : ℝ) * prox ν (x P) (x w) = (B w : ℝ) * prox μ (evalVec s P) (evalVec s w)
    rw [prox_coe ν μ hμν (x P) (x w) (evalVec s P) (evalVec s w) hxP (hx w hw)]
  have hsup : (⨆ i, ν (x P i)) = ⨆ i, μ (evalVec s P i) := by
    congr 1; funext i; rw [← hμν, hxP]
  have hval : ν a = μ (secVal s P k u) := by rw [← hμν, ha]
  rw [hsum, hsup, hval]
  exact hmain

end P2MJB

namespace P2MJB

open ModularCurve

private theorem generalLine_nu (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ)
    (c : modularFunctionFieldBar N → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hmult : ∀ f₁ f₂ : modularFunctionFieldBar N, f₁ ≠ 0 → f₂ ≠ 0 → c (f₁ * f₂) = c f₁ + c f₂)
    (hgreen : ∀ f : modularFunctionFieldBar N, f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, D w = w.ord f) →
      ∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), D P = 0 →
        (D.sum fun w n => (n : ℝ) * g P w) = -Real.log (μ (P.evalAt f)) + c f)
    (hbound : ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P ≠ Q →
      |g P Q - prox μ (evalVec s P) (evalVec s Q)| ≤ lam)
    (hconst : ∀ i : Fin r, |c (s i)| ≤ lam)
    (k : ℕ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0) (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N)
    (ht : 0 < B P → P.ord t = 1) (lamR : ℝ) (hlamR : 0 ≤ lamR)
    (hreg : 0 < B P → ∀ Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, Dt w = w.ord t) →
      |((Dt.erase P).sum fun w n => (n : ℝ) * g P w) - c t
          - (Real.log (⨆ q : Fin r × Fin r, μ (regVal s P t 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)))
              - 2 * Real.log (⨆ i, μ (evalVec s P i)))| ≤ lamR)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : NumberField.FinitePlace ↥L)
    (hμν : ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a)
    (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L)
    (hx : ∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i)
    (hxP : ∀ i, ((x P i : ↥L) : AlgebraicClosure ℚ) = evalVec s P i)
    (cc : ↥L) (hcc : (cc : AlgebraicClosure ℚ) = regVal s P t k (B P).toNat u)
    (y : Fin r × Fin r → ↥L)
    (hy : 0 < B P → ∀ q, ((y q : ↥L) : AlgebraicClosure ℚ)
        = regVal s P t 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) :
    |((B.erase P).sum fun w n => (n : ℝ) * prox ν (x P) (x w))
        - (((k : ℝ) - 2 * (B P : ℝ)) * Real.log (⨆ i, ν (x P i))
            + (B P : ℝ) * Real.log (⨆ q, ν (y q)) - Real.log (ν cc) + c u)|
      ≤ (2 * (embDegree N : ℝ) + 1) * k * lam + (B P : ℝ) * lamR := by
  classical
  have hmain := generalLine N s hs μ hμ g c lam hlam hmult hgreen hbound hconst k u hu0 hu B hB P t ht lamR hlamR hreg

  have hsupp : ∀ w ∈ (B.erase P).support, w ∈ B.support := fun w hw => by
    rw [Finsupp.support_erase] at hw
    exact Finset.mem_of_mem_erase hw
  have hsum : ((B.erase P).sum fun w n => (n : ℝ) * prox ν (x P) (x w))
      = (B.erase P).sum fun w n => (n : ℝ) * prox μ (evalVec s P) (evalVec s w) := by
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun w hw => ?_
    show ((B.erase P) w : ℝ) * prox ν (x P) (x w) = ((B.erase P) w : ℝ) * prox μ (evalVec s P) (evalVec s w)
    rw [prox_coe ν μ hμν (x P) (x w) (evalVec s P) (evalVec s w) hxP (hx w (hsupp w hw))]
  have hsup : (⨆ i, ν (x P i)) = ⨆ i, μ (evalVec s P i) := by
    congr 1; funext i; rw [← hμν, hxP]
  have hval : ν cc = μ (regVal s P t k (B P).toNat u) := by rw [← hμν, hcc]
  rw [hsum, hsup, hval]

  by_cases he : B P = 0
  · rw [he] at hmain ⊢
    push_cast at hmain ⊢
    simp only [mul_zero, zero_mul, sub_zero, zero_add, add_zero] at hmain ⊢
    exact hmain
  · have hBnn : 0 ≤ B P := effective_of_mem hu0 hu B hB P
    have hepos : 0 < B P := lt_of_le_of_ne hBnn (Ne.symm he)
    have hsupy : (⨆ q, ν (y q))
        = ⨆ q : Fin r × Fin r, μ (regVal s P t 1 1 (evalVec s P q.1 • s q.2 - evalVec s P q.2 • s q.1)) := by
      congr 1; funext q; rw [← hμν, hy hepos q]
    rw [hsupy]
    exact hmain

end P2MJB

namespace P2MJB

open AlgebraicCurve ModularCurve

private theorem apply_le_mass {N : ℕ} [NeZero N] (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, 0 ≤ B w) (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (B P : ℝ) ≤ B.sum (fun _ n => (n : ℝ)) := by
  classical
  have h := Finsupp.add_sum_erase' B P (fun _ n => (n : ℝ)) (fun w => by simp)
  have hnn : 0 ≤ (B.erase P).sum (fun _ n => (n : ℝ)) := by
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun w _ => ?_
    by_cases hw : w = P
    · rw [hw, Finsupp.erase_same]; simp
    · rw [Finsupp.erase_ne hw]; exact_mod_cast hB w
  linarith

set_option maxHeartbeats 6400000 in

private theorem jensen_bad_at_main (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (S₀ : Finset ℕ) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        |((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
              + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m)|
          ≤ c₀ * k * (-Real.log (ν (p : ↥L))) := by
  classical

  choose Cp hCp using fun (p : ℕ) (hp : p.Prime) => ModularCurve.exists_greenKernel_regularizedAt_of_prime_of_five_le N hN hN5 s hs 1 p hp
  let Cof : ℕ → ℝ := fun p => if hp : p.Prime then |Cp p hp| else 0
  have hCof0 : ∀ p, 0 ≤ Cof p := fun p => by
    show 0 ≤ (if hp : p.Prime then |Cp p hp| else 0)
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  set Cmax : ℝ := ∑ p ∈ S₀, Cof p with hCmax
  have hCmax : ∀ p ∈ S₀, ∀ hp : p.Prime, Cp p hp ≤ Cmax := by
    intro p hpS hp
    have h1 : Cof p ≤ Cmax := Finset.single_le_sum (fun q _ => hCof0 q) hpS
    have h2 : Cp p hp ≤ Cof p := by
      show Cp p hp ≤ (if hp : p.Prime then |Cp p hp| else 0)
      rw [dif_pos hp]; exact le_abs_self _
    linarith
  set d : ℝ := (embDegree N : ℝ) with hd
  refine ⟨(3 * d + 1) * Cmax, ?_⟩
  intro k u hu0 hu B hB L _ ν p hp hpS hνp x hx
  obtain ⟨μ, hμ, hμν⟩ := NumberField.exists_isNonarchimedean_absoluteValue_extends L ν
  have hcast : (((p : ℕ) : ↥L) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by norm_cast
  have hνμp : ν (p : ↥L) = μ (p : AlgebraicClosure ℚ) := by rw [← hμν, hcast]
  have hμp : μ (p : AlgebraicClosure ℚ) < 1 := hνμp ▸ hνp
  obtain ⟨g, c, hmult, hgreen, hbound, hconst, -, hreg⟩ := hCp p hp μ hμ hμp
  set lam : ℝ := Cp p hp * (-Real.log (μ (p : AlgebraicClosure ℚ))) with hlam_def
  set lam' : ℝ := -Real.log (μ (p : AlgebraicClosure ℚ)) with hlam'_def
  have hlam'0 : 0 ≤ lam' := by
    rw [hlam'_def, neg_nonneg]; exact Real.log_nonpos (apply_nonneg _ _) hμp.le

  obtain ⟨i₀, -⟩ := exists_ord_add_embDivisor_eq_zero N s hs (cuspInftyBar N)
  have hlam0 : 0 ≤ lam := (abs_nonneg _).trans (hconst i₀)
  have hBnn : ∀ w, 0 ≤ B w := effective_of_mem hu0 hu B hB
  refine ⟨-c u, fun v₀ t ht hx₀ cc hcc y hy hy0 => ?_⟩
  have hregv : 0 < B v₀ → ∀ Dt : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, Dt w = w.ord t) →
      |((Dt.erase v₀).sum fun w n => (n : ℝ) * g v₀ w) - c t
          - (Real.log (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)))
              - 2 * Real.log (⨆ i, μ (evalVec s v₀ i)))| ≤ lam :=
    fun hpos Dt hDt => hreg v₀ t (ht hpos) Dt hDt
  have hline := generalLine_nu N s hs μ hμ g c lam hlam0 hmult hgreen hbound hconst k u hu0 hu B hB v₀ t ht lam hlam0
    hregv L ν hμν x hx hx₀ cc hcc y hy

  obtain ⟨Du, hDu, hDudeg⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor u hu0
  have hBmass : B.sum (fun _ n => (n : ℝ)) = (k : ℝ) * embDegree N := mass_eq hu0 B hB Du hDu hDudeg
  have he_le : (B v₀ : ℝ) ≤ (k : ℝ) * d := by rw [hd, ← hBmass]; exact apply_le_mass B hBnn v₀
  have he0 : (0 : ℝ) ≤ (B v₀ : ℝ) := by exact_mod_cast hBnn v₀
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hC : Cp p hp ≤ Cmax := hCmax p hpS hp
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun q _ => hCof0 q
  rw [hνμp]
  have hbd : (2 * d + 1) * k * lam + (B v₀ : ℝ) * lam ≤ (3 * d + 1) * Cmax * k * lam' := by
    have h1 : (B v₀ : ℝ) * lam ≤ (k : ℝ) * d * lam := mul_le_mul_of_nonneg_right he_le hlam0
    have h2 : lam ≤ Cmax * lam' := by rw [hlam_def]; exact mul_le_mul_of_nonneg_right hC hlam'0
    nlinarith [mul_nonneg hk0 hd0, mul_nonneg hk0 hlam'0]
  have := hline

  simp only [sub_neg_eq_add] at this ⊢
  exact this.trans hbd
end P2MJB

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (S₀ : Finset ℕ) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        |((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
              + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m)|
          ≤ c₀ * k * (-Real.log (ν (p : ↥L))) :=
  P2MJB.jensen_bad_at_main N hN hN5 s hs S₀

end S_ModularCurve_JZero_jensen_bad_at_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_bad_at_of_prime_of_five_le (solution)
