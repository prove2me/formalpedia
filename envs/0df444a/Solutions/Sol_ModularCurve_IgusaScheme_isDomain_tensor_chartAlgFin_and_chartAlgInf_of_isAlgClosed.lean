-- Prove2me | solution 1 for ModularCurve.IgusaScheme.isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/205e6ecc-703f-525b-9a0d-72f1b016961d

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_RatPlaceCenterHelpers
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_TensorProductDomain
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
import Theorems.Thm_GaloisRep_charZero_or_charP_of_algebra_ratLocalizedAt
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull jqModC_ne_zero_of_nontrivial coeffEmb modularFunctionFieldBar"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "jFull_ne_zero chartAlg chartAlgFin chartAlgInf chartAlgMid jChartFin inclFin isLocalization_away_inclFin exists_algEquiv_residueField_tensor_chartAlg_chartRing exists_algEquiv_tensor_chartAlg_chartRing"
namespace DOM
p2m_open "ModularCurve.IgusaScheme ModularCurve"

p2m_open "IsLocalRing AlgebraicCurve ModularCurve P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme"
open scoped TensorProduct

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)

scoped instance isPrime_span_ell_int : (Ideal.span {(ℓ : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
  exact Nat.prime_iff_prime_int.mp Fact.out

scoped instance isLocalization_ZL : IsLocalization.AtPrime ℤℓ (Ideal.span {(ℓ : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt Fact.out

theorem ringHom_ext_zl {P : Type*} [Semiring P] (f g : ℤℓ →+* P) : f = g :=
  IsLocalization.ringHom_ext (Ideal.span {(ℓ : ℤ)}).primeCompl (RingHom.ext_int _ _)

def rhoPlace (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) : ℤℓ →+* ↥A :=
  ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap ℤℓ ℚ)).codRestrict A (fun x => by
    refine ValuationSubring.algebraMap_rat_mem_of_not_dvd_den (q := ℓ) Fact.out hA (fun hd => ?_)
    have hcop : (x : ℚ).den.Coprime ℓ := x.2
    exact (Fact.out : ℓ.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm hd))

theorem subtype_comp_rhoPlace (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    A.subtype.comp (rhoPlace ℓ A hA) = algebraMap ℤℓ (AlgebraicClosure ℚ) :=
  RingHom.ext fun _ => rfl

theorem transport (k₀ k : Type*) [Field k₀] [IsAlgClosed k₀] [Field k] [Algebra ℤℓ k₀] [Algebra ℤℓ k]
    [Algebra k₀ k]
    (hFin : IsDomain (k₀ ⊗[ℤℓ] ↥(chartAlgFin N ℓ))) (hInf : IsDomain (k₀ ⊗[ℤℓ] ↥(chartAlgInf N ℓ)))
    (hMid : Nontrivial (k₀ ⊗[ℤℓ] ↥(chartAlgMid N ℓ))) :
    IsDomain (k ⊗[ℤℓ] ↥(chartAlgFin N ℓ)) ∧ IsDomain (k ⊗[ℤℓ] ↥(chartAlgInf N ℓ)) ∧
      Nontrivial (k ⊗[ℤℓ] ↥(chartAlgMid N ℓ)) := by
  haveI := hFin; haveI := hInf; haveI := hMid

  haveI : IsScalarTower ℤℓ k₀ k := IsScalarTower.of_algebraMap_eq' (ringHom_ext_zl ℓ _ _)
  refine ⟨?_, ?_, ?_⟩
  · haveI := IsAlgClosed.isDomain_tensorProduct_of_field k₀ k (k₀ ⊗[ℤℓ] ↥(chartAlgFin N ℓ))
    exact MulEquiv.isDomain (k ⊗[k₀] (k₀ ⊗[ℤℓ] ↥(chartAlgFin N ℓ)))
      (Algebra.TensorProduct.cancelBaseChange ℤℓ k₀ k₀ k ↥(chartAlgFin N ℓ)).symm.toMulEquiv
  · haveI := IsAlgClosed.isDomain_tensorProduct_of_field k₀ k (k₀ ⊗[ℤℓ] ↥(chartAlgInf N ℓ))
    exact MulEquiv.isDomain (k ⊗[k₀] (k₀ ⊗[ℤℓ] ↥(chartAlgInf N ℓ)))
      (Algebra.TensorProduct.cancelBaseChange ℤℓ k₀ k₀ k ↥(chartAlgInf N ℓ)).symm.toMulEquiv
  · haveI : Nontrivial (k ⊗[k₀] (k₀ ⊗[ℤℓ] ↥(chartAlgMid N ℓ))) := inferInstance
    exact (Algebra.TensorProduct.cancelBaseChange ℤℓ k₀ k₀ k ↥(chartAlgMid N ℓ)).symm.toEquiv.nontrivial

theorem nontrivial_tensor_chartAlgMid (k₀ : Type) [Field k₀] [Algebra ℤℓ k₀]
    [IsDomain (k₀ ⊗[ℤℓ] ↥(chartAlgFin N ℓ))]
    (hj : (1 : k₀) ⊗ₜ[ℤℓ] jChartFin N ℓ ≠ 0) :
    Nontrivial (k₀ ⊗[ℤℓ] ↥(chartAlgMid N ℓ)) := by
  let B := k₀ ⊗[ℤℓ] ↥(chartAlgFin N ℓ)
  let L := FractionRing B

  let g : ↥(chartAlgFin N ℓ) →ₐ[ℤℓ] L :=
    (IsScalarTower.toAlgHom ℤℓ B L).comp Algebra.TensorProduct.includeRight
  have hg : ∀ b, g b = algebraMap B L ((1 : k₀) ⊗ₜ[ℤℓ] b) := fun _ => rfl
  have hgj : IsUnit (g.toRingHom (jChartFin N ℓ)) := by
    rw [isUnit_iff_ne_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hg]
    exact fun h => hj (IsFractionRing.injective B L (by rw [h, map_zero]))
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  let gM : ↥(chartAlgMid N ℓ) →+* L := IsLocalization.Away.lift (jChartFin N ℓ) hgj
  have hgM : ∀ b : ↥(chartAlgFin N ℓ), gM (inclFin N ℓ b) = g b := fun b =>
    IsLocalization.Away.lift_eq (jChartFin N ℓ) hgj b
  let gM' : ↥(chartAlgMid N ℓ) →ₐ[ℤℓ] L :=
    { gM with
      commutes' := fun r => by
        have h1 : algebraMap ℤℓ ↥(chartAlgMid N ℓ) r = inclFin N ℓ (algebraMap ℤℓ ↥(chartAlgFin N ℓ) r) :=
          ((inclFin N ℓ).commutes r).symm
        show gM (algebraMap ℤℓ ↥(chartAlgMid N ℓ) r) = algebraMap ℤℓ L r
        rw [h1, hgM, g.commutes] }
  let f : k₀ →ₐ[ℤℓ] L := (IsScalarTower.toAlgHom ℤℓ B L).comp Algebra.TensorProduct.includeLeft
  let Φ : k₀ ⊗[ℤℓ] ↥(chartAlgMid N ℓ) →ₐ[ℤℓ] L :=
    Algebra.TensorProduct.lift f gM' (fun _ _ => Commute.all _ _)
  exact Φ.toRingHom.domain_nontrivial

theorem main_charZero
    (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [Algebra ℤℓ k] :
    IsDomain (k ⊗[ℤℓ] ↥(chartAlgFin N ℓ)) ∧ IsDomain (k ⊗[ℤℓ] ↥(chartAlgInf N ℓ)) ∧
      Nontrivial (k ⊗[ℤℓ] ↥(chartAlgMid N ℓ)) := by
  obtain ⟨⟨eFin, heFin⟩, ⟨eInf, -⟩⟩ := exists_algEquiv_tensor_chartAlg_chartRing N ℓ

  letI : Algebra (AlgebraicClosure ℚ) k :=
    (@IsAlgClosed.lift k _ _ ℚ _ _ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _ _ _).toRingHom.toAlgebra
  haveI dFin : IsDomain (AlgebraicClosure ℚ ⊗[ℤℓ] ↥(chartAlgFin N ℓ)) :=
    Function.Injective.isDomain eFin.toRingEquiv.toRingHom (fun x y h => eFin.toRingEquiv.injective h)
  haveI dInf : IsDomain (AlgebraicClosure ℚ ⊗[ℤℓ] ↥(chartAlgInf N ℓ)) :=
    Function.Injective.isDomain eInf.toRingEquiv.toRingHom (fun x y h => eInf.toRingEquiv.injective h)
  have hj : (1 : AlgebraicClosure ℚ) ⊗ₜ[ℤℓ] jChartFin N ℓ ≠ 0 := by
    intro h
    have h2 := congrArg (fun x => ((eFin x).1 : ↥(modularFunctionFieldBar N)).1) h
    simp only [map_zero, ZeroMemClass.coe_zero] at h2
    rw [heFin] at h2
    have h3 : coeffEmb (AlgebraicClosure ℚ) ((jChartFin N ℓ : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) = 0 := h2
    rw [map_eq_zero_iff _ (coeffEmb (AlgebraicClosure ℚ)).injective, ZeroMemClass.coe_eq_zero] at h3
    exact jFull_ne_zero N h3
  have hMid := nontrivial_tensor_chartAlgMid N ℓ (AlgebraicClosure ℚ) hj
  exact transport N ℓ (AlgebraicClosure ℚ) k dFin dInf hMid

theorem main_charP (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [CharP k ℓ] [IsAlgClosed k] [Algebra ℤℓ k] :
    IsDomain (k ⊗[ℤℓ] ↥(chartAlgFin N ℓ)) ∧ IsDomain (k ⊗[ℤℓ] ↥(chartAlgInf N ℓ)) ∧
      Nontrivial (k ⊗[ℤℓ] ↥(chartAlgMid N ℓ)) := by

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, Fact.out⟩
  haveI : CharP (ResidueField A) ℓ := ValuationSubring.residueField_charP_of_liesOverPrime A Fact.out hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  let ρ := rhoPlace ℓ A hA
  letI : Algebra ℤℓ (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra

  obtain ⟨e0⟩ :=
    ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime A hA
  letI := ZMod.algebra k ℓ
  let ι : ResidueField A →+* k :=
    ((IsAlgClosed.lift : AlgebraicClosure (ZMod ℓ) →ₐ[ZMod ℓ] k) :
      AlgebraicClosure (ZMod ℓ) →+* k).comp e0.toRingHom
  letI : Algebra (ResidueField A) k := ι.toAlgebra

  obtain ⟨⟨eFin, heFin⟩, ⟨eInf, -⟩⟩ := exists_algEquiv_residueField_tensor_chartAlg_chartRing N ℓ hℓN A hA ρ
    (subtype_comp_rhoPlace ℓ A hA)
  haveI dFin : IsDomain (ResidueField A ⊗[ℤℓ] ↥(chartAlgFin N ℓ)) :=
    Function.Injective.isDomain eFin.toRingEquiv.toRingHom (fun x y h => eFin.toRingEquiv.injective h)
  haveI dInf : IsDomain (ResidueField A ⊗[ℤℓ] ↥(chartAlgInf N ℓ)) :=
    Function.Injective.isDomain eInf.toRingEquiv.toRingHom (fun x y h => eInf.toRingEquiv.injective h)
  have hj : (1 : ResidueField A) ⊗ₜ[ℤℓ] jChartFin N ℓ ≠ 0 := by
    intro h
    have h2 := congrArg (fun x => (eFin x).1) h
    simp only [map_zero, ZeroMemClass.coe_zero] at h2
    rw [heFin] at h2
    exact jqModC_ne_zero_of_nontrivial (ResidueField A) (congrArg Subtype.val h2)
  have hMid := nontrivial_tensor_chartAlgMid N ℓ (ResidueField A) hj
  exact transport N ℓ (ResidueField A) k dFin dInf hMid

theorem main (hℓN : ¬ ℓ ∣ N) (k : Type) [Field k] [IsAlgClosed k] [Algebra ℤℓ k] :
    IsDomain (k ⊗[ℤℓ] ↥(chartAlgFin N ℓ)) ∧ IsDomain (k ⊗[ℤℓ] ↥(chartAlgInf N ℓ)) ∧
      Nontrivial (k ⊗[ℤℓ] ↥(chartAlgMid N ℓ)) := by
  rcases GaloisRep.charZero_or_charP_of_algebra_ratLocalizedAt ℓ k with h0 | hℓ
  · exact main_charZero N ℓ k
  · exact main_charP N ℓ hℓN k

end ModularCurve.IgusaScheme.DOM
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme.DOM"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme.DOM"

open scoped TensorProduct in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve _root_.ModularCurve.IgusaScheme _root_.P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed.ModularCurve.IgusaScheme in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) k] :
    IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ)) ∧
      IsDomain (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ)) ∧
      Nontrivial (k ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgMid N ℓ)) :=
  ModularCurve.IgusaScheme.DOM.main N ℓ hℓN k

end S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_isDomain_tensor_chartAlgFin_and_chartAlgInf_of_isAlgClosed (solution)
