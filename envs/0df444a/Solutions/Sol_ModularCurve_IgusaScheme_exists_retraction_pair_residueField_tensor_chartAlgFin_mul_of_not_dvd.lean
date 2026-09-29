-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/cfdeb8b0-8854-52cb-bc24-064aa8322510

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_LaurentBaseChangeTower
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct
p2m_open "IsLocalRing ModularCurve ModularCurve.IgusaScheme AlgebraicCurve~CurveModel Polynomial"

namespace IgusaFibreComponents

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "ℤp" => ↥(GaloisRep.ratLocalizedAt p)
set_option quotPrecheck false in
local notation "Q̄" => AlgebraicClosure ℚ

abbrev FF (M : ℕ) [NeZero M] : Type := ↥(modularFunctionFieldFull M)

abbrev FB (M : ℕ) [NeZero M] : Type := ↥(modularFunctionFieldBar M)

abbrev LC (κ : Type) [Field κ] (M : ℕ) [NeZero M] : Type := ↥(modularFunctionFieldFullC κ M)

def jt (κ : Type) [Field κ] (M : ℕ) [NeZero M] : LC κ M := ⟨jqModC κ, jqModC_mem_full κ M⟩

@[scoped simp] theorem coe_jt (κ : Type) [Field κ] (M : ℕ) [NeZero M] : (jt κ M : LaurentSeries κ) = jqModC κ := rfl

theorem not_dvd_one' (hp : Fact p.Prime) : ¬ p ∣ 1 := fun h => hp.out.ne_one (Nat.dvd_one.mp h)

theorem coe_ratHom (M : ℕ) [NeZero M] (φ : ℚ →+* FF M) (r : ℚ) :
    ((φ r : FF M) : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) r := by
  have h : ((modularFunctionFieldFull M).toSubalgebra.val.toRingHom.comp φ) =
      algebraMap ℚ (LaurentSeries ℚ) := Subsingleton.elim _ _
  exact RingHom.congr_fun h r

theorem coe_algebraMap_int (M : ℕ) [NeZero M] (c : ℤp) :
    ((algebraMap ℤp (FF M) c : FF M) : LaurentSeries ℚ) =
      algebraMap ℚ (LaurentSeries ℚ) (c : ℚ) := by
  rw [IsScalarTower.algebraMap_apply ℤp ℚ (FF M)]
  exact coe_ratHom M _ _

def incl : FF N →ₐ[ℤp] FF (N * p) where
  toFun f := ⟨(f : LaurentSeries ℚ), full_degeneracy_le (dvd_mul_right N p) f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    apply Subtype.ext
    show ((algebraMap ℤp (FF N) c : FF N) : LaurentSeries ℚ) =
      ((algebraMap ℤp (FF (N * p)) c : FF (N * p)) : LaurentSeries ℚ)
    rw [coe_algebraMap_int p N c, coe_algebraMap_int p (N * p) c]

theorem incl_apply (f : FF N) :
    incl N p f = ⟨(f : LaurentSeries ℚ), full_degeneracy_le (dvd_mul_right N p) f.2⟩ := rfl

theorem coe_incl (f : FF N) : ((incl N p f : FF (N * p)) : LaurentSeries ℚ) = f := by
  rw [incl_apply]

theorem incl_injective : Function.Injective (incl N p) := fun f g h =>
  Subtype.ext (by simpa only [incl_apply, Subtype.mk.injEq] using h)

theorem incl_jFull : incl N p (jFull N) = jFull (N * p) := by
  rw [incl_apply]; rfl

theorem map_incl_adjoin : (Algebra.adjoin ℤp ({jFull N} : Set (FF N))).map (incl N p) =
      Algebra.adjoin ℤp ({jFull (N * p)} : Set (FF (N * p))) := by
  rw [AlgHom.map_adjoin, Set.image_singleton, incl_jFull]

theorem incl_mem_adjoin {x : FF N} (hx : x ∈ Algebra.adjoin ℤp ({jFull N} : Set (FF N))) :
    incl N p x ∈ Algebra.adjoin ℤp ({jFull (N * p)} : Set (FF (N * p))) := by
  rw [← map_incl_adjoin]
  exact Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩

def inclAdjoin : ↥(Algebra.adjoin ℤp ({jFull N} : Set (FF N))) →+*
    ↥(Algebra.adjoin ℤp ({jFull (N * p)} : Set (FF (N * p)))) :=
  (((incl N p).comp (Algebra.adjoin ℤp ({jFull N} : Set (FF N))).val).codRestrict
    (Algebra.adjoin ℤp ({jFull (N * p)} : Set (FF (N * p)))) (fun x => incl_mem_adjoin N p x.2)).toRingHom

theorem isIntegral_incl {x : FF N} (hx : IsIntegral (Algebra.adjoin ℤp ({jFull N} : Set (FF N))) x) :
    IsIntegral (Algebra.adjoin ℤp ({jFull (N * p)} : Set (FF (N * p)))) (incl N p x) :=
  hx.map_of_comp_eq (inclAdjoin N p) (incl N p).toRingHom (by ext; rfl)

def ι : ↥(chartAlgFin N p) →ₐ[ℤp] ↥(chartAlgFin (N * p) p) :=
  ((incl N p).comp (chartAlgFin N p).val).codRestrict (chartAlgFin (N * p) p)
    (fun b => (mem_chartAlg_iff (N * p) p).mpr (isIntegral_incl N p ((mem_chartAlg_iff N p).mp b.2)))

theorem coe_ι (b : ↥(chartAlgFin N p)) :
    ((ι N p b : ↥(chartAlgFin (N * p) p)) : FF (N * p)) = incl N p b := rfl

theorem coe_coe_ι (b : ↥(chartAlgFin N p)) :
    (((ι N p b : ↥(chartAlgFin (N * p) p)) : FF (N * p)) : LaurentSeries ℚ) =
      ((b : FF N) : LaurentSeries ℚ) := by
  rw [coe_ι, coe_incl]

theorem ι_jChartFin : ι N p (jChartFin N p) = jChartFin (N * p) p := by
  apply Subtype.ext
  rw [coe_ι, coe_jChartFin, incl_jFull, coe_jChartFin]

theorem ι_injective : Function.Injective (ι N p) := fun a b h =>
  Subtype.ext (incl_injective N p (by rw [← coe_ι, ← coe_ι, h]))

def jd (d : ℕ) [NeZero d] (hd : d ∣ N) : FF N := ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩

@[scoped simp] theorem coe_jd (d : ℕ) [NeZero d] (hd : d ∣ N) : (jd N d hd : LaurentSeries ℚ) = qExpand ℚ d jq := rfl

theorem jd_mem_chartAlgFin (d : ℕ) [NeZero d] (hd : d ∣ N) : jd N d hd ∈ chartAlgFin N p := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData d
  rw [mem_chartAlg_iff]
  set R := Algebra.adjoin ℤp ({jFull N} : Set (FF N)) with hR
  let jR : R := ⟨jFull N, Algebra.self_mem_adjoin_singleton ℤp (jFull N)⟩
  let φ : ℤ[X] →+* R := (Polynomial.aeval jR).toRingHom
  refine ⟨data.Φ.map φ, data.monic.map φ, ?_⟩
  rw [Polynomial.eval₂_map]
  apply Subtype.val_injective
  have hval := Polynomial.hom_eval₂ data.Φ ((algebraMap R (FF N)).comp φ)
    (modularFunctionFieldFull N).toSubalgebra.val.toRingHom (jd N d hd)
  have hcomp : (modularFunctionFieldFull N).toSubalgebra.val.toRingHom.comp
      ((algebraMap R (FF N)).comp φ) = evalAtJ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [map_intCast]
    · rw [evalAtJ_X]
      show (((algebraMap R (FF N)) (Polynomial.aeval jR X) : FF N) : LaurentSeries ℚ) = jq
      rw [Polynomial.aeval_X]
      rfl
  rw [hcomp] at hval
  show (modularFunctionFieldFull N).toSubalgebra.val.toRingHom
      (Polynomial.eval₂ ((algebraMap R (FF N)).comp φ) (jd N d hd) data.Φ) = ((0 : FF N) : LaurentSeries ℚ)
  rw [hval]
  exact data.eval_eq_zero

def jdO (d : ℕ) [NeZero d] (hd : d ∣ N) : ↥(chartAlgFin N p) := ⟨jd N d hd, jd_mem_chartAlgFin N p d hd⟩

theorem coe_jdO (d : ℕ) [NeZero d] (hd : d ∣ N) : (jdO N p d hd : FF N) = jd N d hd := rfl

section Bivariate

variable (M : ℕ) [NeZero M]

abbrev evJ : ℤp[X] →+* ↥(chartAlgFin M p) := (Polynomial.aeval (jChartFin M p)).toRingHom

theorem val_comp_evJ : (chartAlgFin M p).val.toRingHom.comp (evJ p M) =
    (Polynomial.aeval (jFull M) : ℤp[X] →ₐ[ℤp] FF M).toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp
  · simp [coe_jChartFin]

theorem exists_bivariate (b : ↥(chartAlgFin M p)) :
    ∃ P : Polynomial (Polynomial ℤp), P.Monic ∧ P.eval₂ (evJ p M) b = 0 := by
  classical
  obtain ⟨P₁, hmonic, hroot⟩ := (mem_chartAlg_iff M p).mp b.2

  have hlifts : P₁.map (algebraMap _ (FF M)) ∈
      Polynomial.lifts (Polynomial.aeval (jFull M) : ℤp[X] →ₐ[ℤp] FF M).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    have hk : ((P₁.coeff k : ↥(Algebra.adjoin ℤp ({jFull M} : Set (FF M)))) : FF M) ∈
        (Polynomial.aeval (jFull M) : ℤp[X] →ₐ[ℤp] FF M).range :=
      (SetLike.ext_iff.mp (Algebra.adjoin_singleton_eq_range_aeval ℤp (jFull M)) _).mp (P₁.coeff k).2
    obtain ⟨Q, hQ⟩ := (AlgHom.mem_range _).mp hk
    exact ⟨Q, hQ⟩
  obtain ⟨P, hPmap, -, hPmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hmonic.map _)
  refine ⟨P, hPmonic, ?_⟩
  apply Subtype.val_injective
  have h1 := Polynomial.hom_eval₂ P (evJ p M) (chartAlgFin M p).val.toRingHom b
  rw [val_comp_evJ] at h1
  rw [show ((chartAlgFin M p).val.toRingHom (Polynomial.eval₂ (evJ p M) b P)) =
      ((Polynomial.eval₂ (evJ p M) b P : ↥(chartAlgFin M p)) : FF M) from rfl] at h1
  rw [h1, ← Polynomial.eval_map, hPmap, Polynomial.eval_map]
  exact hroot

end Bivariate

abbrev emb (M : ℕ) [NeZero M] : FF M →+* FB M := baseChangeRingHom Q̄ (modularFunctionFieldFull M)

theorem coe_emb (M : ℕ) [NeZero M] (f : FF M) : (emb M f : LaurentSeries Q̄) = coeffEmb Q̄ (f : LaurentSeries ℚ) :=
  coe_baseChangeRingHom Q̄ _ f

def J (M : ℕ) [NeZero M] : FB M :=
  ⟨coeffEmb Q̄ jq, coeffEmb_mem_laurentBaseChange Q̄ (modularFunctionField_le_full M (jq_mem M))⟩

theorem emb_jFull (M : ℕ) [NeZero M] : emb M (jFull M) = J M := by
  apply Subtype.ext; rw [coe_emb]; rfl

abbrev W : FB (N * p) ≃ₐ[Q̄] FB (N * p) := geomAut Q̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p)

theorem W_emb (f : FF (N * p)) : W N p (emb (N * p) f) = emb (N * p) (atkinLehnerInvolutionFull N p f) := by
  apply Subtype.ext
  rw [coe_emb]
  have := coe_geomAut_coeffEmb Q̄ (modularFunctionFieldFull (N * p)) (atkinLehnerInvolutionFull N p) f
  rw [← this]
  rfl

structure Ctx where
  A : ValuationSubring Q̄
  hA : A.LiesOverPrime p
  charP : CharP (ResidueField ↥A) p
  algClosed : IsAlgClosed (ResidueField ↥A)
  R : Fin 2 → RegularProlongation A (FB (N * p)) (LC (ResidueField ↥A) N)
  h1b : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * p)),
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : FB (N * p)) ∈ (R 0).integers,
      (((R 0).residue ⟨_, hint⟩ : LC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) =
        coeffMap (residue ↥A) y
  h2 : ∀ f : FB (N * p), f ∈ (R 1).integers ↔ W N p f ∈ (R 0).integers
  h2b : ∀ (f : FB (N * p)) (h₁ : f ∈ (R 1).integers) (h₀ : W N p f ∈ (R 0).integers),
    (R 1).residue ⟨f, h₁⟩ = (R 0).residue ⟨_, h₀⟩
  hj : ∀ i, J (N * p) ∈ (R i).integers
  hres0 : (((R 0).residue ⟨_, hj 0⟩ : LC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) =
    jqModC (ResidueField ↥A)
  hres1 : (((R 1).residue ⟨_, hj 1⟩ : LC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) =
    jqModC (ResidueField ↥A) ^ p
  ρ : ℤp →+* ↥A
  hρ : A.subtype.comp ρ = algebraMap ℤp Q̄
  w : ↥(chartAlgFin (N * p) p) ≃ₐ[ℤp] ↥(chartAlgFin (N * p) p)
  hw : ∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : FF (N * p)) = atkinLehnerInvolutionFull N p (b : FF (N * p))
  hww : w.trans w = AlgEquiv.refl
  hpN : ¬ p ∣ N

namespace Ctx

variable {N p}
variable (C : Ctx N p)

abbrev κ : Type := ResidueField ↥C.A

scoped instance instCharP : CharP C.κ p := C.charP
scoped instance instAlgClosed : IsAlgClosed C.κ := C.algClosed

scoped instance instAlg : Algebra ℤp C.κ := ((residue ↥C.A).comp C.ρ).toAlgebra

theorem algebraMap_κ (c : ℤp) : algebraMap ℤp C.κ c = residue ↥C.A (C.ρ c) := rfl

theorem emb_algebraMap (c : ℤp) :
    emb (N * p) (algebraMap ℤp (FF (N * p)) c) = algebraMap Q̄ (FB (N * p)) ((C.ρ c : ↥C.A) : Q̄) := by
  apply Subtype.ext
  have hR : ∀ y : Q̄, ((algebraMap Q̄ (FB (N * p)) y : FB (N * p)) : LaurentSeries Q̄) =
      algebraMap Q̄ (LaurentSeries Q̄) y := fun y => rfl
  rw [coe_emb, coe_algebraMap_int, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, hR,
    algebraMap_laurentSeries_eq_single]
  congr 1
  have h := RingHom.congr_fun C.hρ c
  simp only [RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype] at h
  rw [h, IsScalarTower.algebraMap_apply ℤp ℚ Q̄]
  rfl

theorem emb_adjoin_mem (i : Fin 2) {x : FF (N * p)}
    (hx : x ∈ Algebra.adjoin ℤp ({jFull (N * p)} : Set (FF (N * p)))) :
    emb (N * p) x ∈ (C.R i).integers := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [emb_jFull]
    exact C.hj i
  | algebraMap c =>
    rw [C.emb_algebraMap]
    exact ((C.R i).algebraMap_mem_iff _).mpr (C.ρ c).2
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem coe_aeval_jChartFin (M : ℕ) [NeZero M] (Q : ℤp[X]) :
    ((Polynomial.aeval (jChartFin M p) Q : ↥(chartAlgFin M p)) : FF M) = Polynomial.aeval (jFull M) Q := by
  rw [← coe_jChartFin M p]
  exact (Polynomial.aeval_algHom_apply (chartAlgFin M p).val (jChartFin M p) Q).symm

theorem emb_mem (i : Fin 2) (b : ↥(chartAlgFin (N * p) p)) : emb (N * p) (b : FF (N * p)) ∈ (C.R i).integers := by
  obtain ⟨P, hPmonic, hProot⟩ := exists_bivariate p (N * p) b
  set θ : ℤp[X] →+* FB (N * p) :=
    (emb (N * p)).comp ((chartAlgFin (N * p) p).val.toRingHom.comp (evJ p (N * p))) with hθdef
  have hθ : ∀ Q : ℤp[X], θ Q ∈ (C.R i).integers := by
    intro Q
    refine C.emb_adjoin_mem i ?_
    show ((Polynomial.aeval (jChartFin (N * p) p) Q : ↥(chartAlgFin (N * p) p)) : FF (N * p)) ∈ _
    rw [coe_aeval_jChartFin]
    exact Polynomial.aeval_mem_adjoin_singleton ℤp (jFull (N * p))
  let V := (C.R i).integers
  let θ' : ℤp[X] →+* ↥V := θ.codRestrict V.toSubring hθ
  have hint : IsIntegral ↥V (emb (N * p) (b : FF (N * p))) := by
    refine ⟨P.map θ', hPmonic.map θ', ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥V (FB (N * p))).comp θ' = θ := RingHom.ext fun Q => rfl
    rw [hcomp]
    have h1 := Polynomial.hom_eval₂ P (evJ p (N * p))
      ((emb (N * p)).comp (chartAlgFin (N * p) p).val.toRingHom) b
    rw [hProot, map_zero] at h1
    exact h1.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

def toV (i : Fin 2) : ↥(chartAlgFin (N * p) p) →+* ↥(C.R i).integers :=
  ((emb (N * p)).comp (chartAlgFin (N * p) p).val.toRingHom).codRestrict (C.R i).integers.toSubring
    (fun b => C.emb_mem i b)

theorem coe_toV (i : Fin 2) (b : ↥(chartAlgFin (N * p) p)) :
    (C.toV i b : FB (N * p)) = emb (N * p) (b : FF (N * p)) := rfl

def r (i : Fin 2) : ↥(chartAlgFin (N * p) p) →+* LC C.κ N := (C.R i).residue.comp (C.toV i)

theorem r_apply (i : Fin 2) (b : ↥(chartAlgFin (N * p) p)) : C.r i b = (C.R i).residue (C.toV i b) := rfl

theorem residue_congr (i : Fin 2) {x y : ↥(C.R i).integers} (h : (x : FB (N * p)) = y) :
    (C.R i).residue x = (C.R i).residue y := by
  rw [Subtype.ext h]

theorem r_algebraMap (i : Fin 2) (c : ℤp) :
    C.r i (algebraMap ℤp _ c) = algebraMap C.κ (LC C.κ N) (algebraMap ℤp C.κ c) := by
  rw [algebraMap_κ, r_apply, ← (C.R i).residue_algebraMap (C.ρ c)]
  apply residue_congr
  rw [coe_toV, Subalgebra.coe_algebraMap]
  exact C.emb_algebraMap c

theorem r_zero_j : C.r 0 (jChartFin (N * p) p) = jt C.κ N := by
  apply Subtype.ext
  rw [coe_jt, ← C.hres0, r_apply,
    C.residue_congr 0 (show (C.toV 0 (jChartFin (N * p) p) : FB (N * p)) =
        ((⟨J (N * p), C.hj 0⟩ : ↥(C.R 0).integers) : FB (N * p)) from by
      rw [coe_toV, coe_jChartFin, emb_jFull])]

theorem r_one_j : C.r 1 (jChartFin (N * p) p) = jt C.κ N ^ p := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_jt, ← C.hres1, r_apply,
    C.residue_congr 1 (show (C.toV 1 (jChartFin (N * p) p) : FB (N * p)) =
        ((⟨J (N * p), C.hj 1⟩ : ↥(C.R 1).integers) : FB (N * p)) from by
      rw [coe_toV, coe_jChartFin, emb_jFull])]

theorem r_zero_of_coeffMap (b : ↥(chartAlgFin (N * p) p)) (y : LaurentSeries ↥C.A)
    (hy : coeffMap C.A.subtype y = coeffEmb Q̄ ((b : FF (N * p)) : LaurentSeries ℚ)) :
    ((C.r 0 b : LC C.κ N) : LaurentSeries C.κ) = coeffMap (residue ↥C.A) y := by
  have hmem : coeffMap C.A.subtype y ∈ modularFunctionFieldBar (N * p) := by
    rw [hy]; exact coeffEmb_mem_laurentBaseChange Q̄ (b : FF (N * p)).2
  obtain ⟨hint, hres⟩ := C.h1b y hmem
  rw [← hres, r_apply, C.residue_congr 0 (show (C.toV 0 b : FB (N * p)) =
      ((⟨⟨coeffMap C.A.subtype y, hmem⟩, hint⟩ : ↥(C.R 0).integers) : FB (N * p)) from by
    rw [coe_toV]; apply Subtype.ext; rw [coe_emb]; exact hy.symm)]

theorem coe_r_zero_jd (d : ℕ) [NeZero d] (hd : d ∣ N) :
    ((C.r 0 (ι N p (jdO N p d hd)) : LC C.κ N) : LaurentSeries C.κ) = qExpand C.κ d (jqModC C.κ) := by
  rw [C.r_zero_of_coeffMap (ι N p (jdO N p d hd)) (qExpand ↥C.A d (jqModC ↥C.A))]
  · rw [coeffMap_qExpand, coeffMap_jqModC]
  · rw [coeffMap_qExpand, coeffMap_jqModC, coe_coe_ι, coe_jdO, coe_jd, coeffEmb, coeffMap_qExpand,
      ← jqModC_rat, coeffMap_jqModC]

theorem w_w (b : ↥(chartAlgFin (N * p) p)) : C.w (C.w b) = b := by
  have := congrArg (fun e => e b) C.hww
  simpa using this

theorem r_one_eq (b : ↥(chartAlgFin (N * p) p)) : C.r 1 b = C.r 0 (C.w b) := by
  rw [r_apply, r_apply]
  have h₀ : W N p (C.toV 1 b : FB (N * p)) ∈ (C.R 0).integers := (C.h2 _).mp (C.toV 1 b).2
  rw [show C.toV 1 b = ⟨(C.toV 1 b : FB (N * p)), (C.toV 1 b).2⟩ from rfl, C.h2b _ (C.toV 1 b).2 h₀]
  apply residue_congr
  show W N p (C.toV 1 b : FB (N * p)) = (C.toV 0 (C.w b) : FB (N * p))
  rw [coe_toV, coe_toV, W_emb, C.hw]

theorem isAL (hpN : ¬ p ∣ N) : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p (Fact.out) hpN)

theorem coe_w_j : (((C.w (jChartFin (N * p) p) : ↥(chartAlgFin (N * p) p)) : FF (N * p)) : LaurentSeries ℚ) =
    qExpand ℚ p jq := by
  rw [C.hw, coe_jChartFin]
  have h1 := (isAL C.hpN 1 inferInstance (one_dvd N)).1
  have hj : (⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ : FF (N * p)) =
      jFull (N * p) := Subtype.ext (qExpand_one_apply jq)
  rw [hj] at h1
  rw [h1]
  exact qExpand_congr (Nat.one_mul p) jq

theorem r_zero_wj : C.r 0 (C.w (jChartFin (N * p) p)) = jt C.κ N ^ p := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_jt,
    C.r_zero_of_coeffMap (C.w (jChartFin (N * p) p)) (qExpand ↥C.A p (jqModC ↥C.A))]
  · rw [coeffMap_qExpand, coeffMap_jqModC, qExpand_jqModC_eq_pow_unconditional]
  · rw [coeffMap_qExpand, coeffMap_jqModC, C.coe_w_j, coeffEmb, coeffMap_qExpand, ← jqModC_rat,
      coeffMap_jqModC]

theorem r_one_wj : C.r 1 (C.w (jChartFin (N * p) p)) = jt C.κ N := by
  rw [C.r_one_eq, C.w_w, r_zero_j]

theorem isIntegral_adjoin_of_eval₂ {L : Type} [Field L] [Algebra C.κ L] (s t x : L)
    (ht : t ∈ Algebra.adjoin C.κ ({s} : Set L)) (P : Polynomial (Polynomial C.κ)) (hP : P.Monic)
    (h : P.eval₂ (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L).toRingHom x = 0) :
    IsIntegral (Algebra.adjoin C.κ ({s} : Set L)) x := by
  let θ : C.κ[X] →+* ↥(Algebra.adjoin C.κ ({s} : Set L)) :=
    (Polynomial.aeval (⟨t, ht⟩ : ↥(Algebra.adjoin C.κ ({s} : Set L)))).toRingHom
  refine ⟨P.map θ, hP.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap ↥(Algebra.adjoin C.κ ({s} : Set L)) L).comp θ =
      (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · show ((Polynomial.aeval (⟨t, ht⟩ : ↥(Algebra.adjoin C.κ ({s} : Set L))) (Polynomial.C c) :
          ↥(Algebra.adjoin C.κ ({s} : Set L))) : L) = (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L) (Polynomial.C c)
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Subalgebra.coe_algebraMap]
    · show ((Polynomial.aeval (⟨t, ht⟩ : ↥(Algebra.adjoin C.κ ({s} : Set L))) (Polynomial.X) :
          ↥(Algebra.adjoin C.κ ({s} : Set L))) : L) = (Polynomial.aeval t : C.κ[X] →ₐ[C.κ] L) Polynomial.X
      rw [Polynomial.aeval_X, Polynomial.aeval_X]
  rw [hcomp]
  exact h

theorem r_comp_evJ (i : Fin 2) :
    (C.r i).comp (evJ p (N * p)) =
      (Polynomial.aeval (C.r i (jChartFin (N * p) p)) : C.κ[X] →ₐ[C.κ] LC C.κ N).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap ℤp C.κ)) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C]
    rw [C.r_algebraMap]
  · simp

theorem r_j_mem_adjoin (i : Fin 2) :
    C.r i (jChartFin (N * p) p) ∈ Algebra.adjoin C.κ ({jt C.κ N} : Set (LC C.κ N)) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [r_zero_j]
    exact Algebra.self_mem_adjoin_singleton _ _
  · rw [r_one_j]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ _) p

theorem r_mem_chartRing (i : Fin 2) (b : ↥(chartAlgFin (N * p) p)) :
    C.r i b ∈ CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)) := by
  rw [CurveModel.mem_chartRing_iff]
  obtain ⟨P, hPmonic, hProot⟩ := exists_bivariate p (N * p) b
  refine C.isIntegral_adjoin_of_eval₂ (jt C.κ N) (C.r i (jChartFin (N * p) p)) (C.r i b) (C.r_j_mem_adjoin i)
    (P.map (Polynomial.mapRingHom (algebraMap ℤp C.κ))) (hPmonic.map _) ?_
  rw [Polynomial.eval₂_map, ← r_comp_evJ, ← Polynomial.hom_eval₂, hProot, map_zero]

section Fibre

variable (M : ℕ) [NeZero M]

abbrev B : Type := C.κ ⊗[ℤp] ↥(chartAlgFin M p)

abbrev fB : C.κ[X] →+* C.B M :=
  (Polynomial.aeval ((1 : C.κ) ⊗ₜ[ℤp] jChartFin M p) : C.κ[X] →ₐ[C.κ] C.B M).toRingHom

theorem algebraMap_B_int (c : ℤp) : algebraMap ℤp (C.B M) c = algebraMap C.κ (C.B M) (algebraMap ℤp C.κ c) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem includeRight_comp_evJ :
    (Algebra.TensorProduct.includeRight : ↥(chartAlgFin M p) →ₐ[ℤp] C.B M).toRingHom.comp (evJ p M) =
      (C.fB M).comp (Polynomial.mapRingHom (algebraMap ℤp C.κ)) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C, AlgHom.commutes]
    exact C.algebraMap_B_int M c
  · simp

theorem isIntegralElem_B (z : C.B M) : (C.fB M).IsIntegralElem z := by
  induction z using TensorProduct.induction_on with
  | zero => simpa using (C.fB M).isIntegralElem_map (x := 0)
  | tmul x b =>
    have hx : (C.fB M).IsIntegralElem (x ⊗ₜ[ℤp] (1 : ↥(chartAlgFin M p))) := by
      have : (C.fB M) (Polynomial.C x) = x ⊗ₜ[ℤp] (1 : ↥(chartAlgFin M p)) := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [← this]
      exact (C.fB M).isIntegralElem_map
    have hb : (C.fB M).IsIntegralElem ((1 : C.κ) ⊗ₜ[ℤp] b) := by
      obtain ⟨P, hPmonic, hProot⟩ := exists_bivariate p M b
      refine ⟨P.map (Polynomial.mapRingHom (algebraMap ℤp C.κ)), hPmonic.map _, ?_⟩
      have h1 := Polynomial.hom_eval₂ P (evJ p M)
        (Algebra.TensorProduct.includeRight : ↥(chartAlgFin M p) →ₐ[ℤp] C.B M).toRingHom b
      rw [hProot, map_zero, includeRight_comp_evJ] at h1
      rw [Polynomial.eval₂_map]
      exact h1.symm
    have := hx.mul (C.fB M) hb
    rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
  | add x y hx hy => exact hx.add _ hy

end Fibre

scoped instance instAlgLC : Algebra ℤp (LC C.κ N) := ((algebraMap C.κ (LC C.κ N)).comp (algebraMap ℤp C.κ)).toAlgebra

scoped instance instTowerLC : IsScalarTower ℤp C.κ (LC C.κ N) := IsScalarTower.of_algebraMap_eq' rfl

def rAlg (i : Fin 2) : ↥(chartAlgFin (N * p) p) →ₐ[ℤp] LC C.κ N :=
  { C.r i with
    commutes' := fun c => by
      show C.r i (algebraMap ℤp _ c) = _
      rw [C.r_algebraMap, IsScalarTower.algebraMap_apply ℤp C.κ (LC C.κ N)] }

@[scoped simp] theorem rAlg_apply (i : Fin 2) (b) : C.rAlg i b = C.r i b := rfl

def Φ (i : Fin 2) : C.B (N * p) →ₐ[C.κ] LC C.κ N :=
  Algebra.TensorProduct.lift (Algebra.ofId C.κ (LC C.κ N)) (C.rAlg i) (fun _ _ => Commute.all _ _)

theorem Φ_tmul (i : Fin 2) (x : C.κ) (b : ↥(chartAlgFin (N * p) p)) :
    C.Φ i (x ⊗ₜ[ℤp] b) = algebraMap C.κ (LC C.κ N) x * C.r i b := by
  rw [Φ, Algebra.TensorProduct.lift_tmul]
  rfl

theorem Φ_one_tmul (i : Fin 2) (b : ↥(chartAlgFin (N * p) p)) : C.Φ i (1 ⊗ₜ[ℤp] b) = C.r i b := by
  rw [Φ_tmul, map_one, one_mul]

theorem Φ_fB (i : Fin 2) (Q : C.κ[X]) :
    C.Φ i (C.fB (N * p) Q) = Polynomial.aeval (C.r i (jChartFin (N * p) p)) Q := by
  show C.Φ i (Polynomial.aeval _ Q) = _
  rw [← Polynomial.aeval_algHom_apply, Φ_one_tmul]

theorem Φ_mem_chartRing (i : Fin 2) (z : C.B (N * p)) :
    C.Φ i z ∈ CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul x b =>
    rw [Φ_tmul]
    exact mul_mem (Subalgebra.algebraMap_mem _ x) (C.r_mem_chartRing i b)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem transcendental_r_j (i : Fin 2) : Transcendental C.κ (C.r i (jChartFin (N * p) p)) := by
  have key : ∀ e : ℕ, 0 < e → Transcendental C.κ (jt C.κ N ^ e) := by
    intro e he
    have ht : Transcendental C.κ (jqModC C.κ ^ e) := (transcendental_jqModC C.κ).pow he
    rw [transcendental_iff] at ht ⊢
    intro Q hQ
    apply ht Q
    have h0 := congrArg (fun y : LC C.κ N => (y : LaurentSeries C.κ)) hQ
    simp only [ZeroMemClass.coe_zero] at h0
    have h1 : Polynomial.aeval (((jt C.κ N ^ e : LC C.κ N)) : LaurentSeries C.κ) Q =
        ((Polynomial.aeval (jt C.κ N ^ e) Q : LC C.κ N) : LaurentSeries C.κ) :=
      Polynomial.aeval_algHom_apply (modularFunctionFieldFullC C.κ N).val (jt C.κ N ^ e) Q
    rw [SubmonoidClass.coe_pow, coe_jt] at h1
    rw [h1, h0]
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [r_zero_j]
    simpa using key 1 one_pos
  · rw [r_one_j]
    exact key p (Fact.out : p.Prime).pos

theorem comap_ker_Φ (i : Fin 2) : (RingHom.ker (C.Φ i)).comap (C.fB (N * p)) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun Q hQ => ?_
  rw [Ideal.mem_comap, RingHom.mem_ker, Φ_fB] at hQ
  exact (transcendental_iff.mp (C.transcendental_r_j i)) Q hQ

theorem ker_Φ_mem_minimalPrimes (i : Fin 2) : RingHom.ker (C.Φ i) ∈ minimalPrimes (C.B (N * p)) := by
  haveI hprime : (RingHom.ker (C.Φ i)).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hprime, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hle
  by_contra hnot
  obtain ⟨x, hxK, hxq⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨P, hPmonic, hProot⟩ := C.isIntegralElem_B (N * p) x
  haveI := hq
  have hlt := Ideal.comap_lt_comap_of_root_mem_sdiff (f := C.fB (N * p)) hle ⟨hxK, hxq⟩
    (p := P) ?_ (by rw [hProot]; exact q.zero_mem)
  · rw [comap_ker_Φ] at hlt
    exact not_lt_bot hlt
  · haveI : Nontrivial (C.κ[X] ⧸ Ideal.comap (C.fB (N * p)) q) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.comap_ne_top _ hq.ne_top)
    exact (hPmonic.map _).ne_zero

abbrev mapw : C.B (N * p) →ₐ[C.κ] C.B (N * p) := Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) (C.w : _ →ₐ[ℤp] _)

theorem Φ_one_eq_Φ_zero_mapw (z : C.B (N * p)) : C.Φ 1 z = C.Φ 0 (C.mapw z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_algHom, Φ_tmul, Φ_tmul, r_one_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mapw_mapw (z : C.B (N * p)) : C.mapw (C.mapw z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; simp [C.w_w]
  | add x y hx hy => simp only [map_add, hx, hy]

abbrev mapι : C.B N →ₐ[C.κ] C.B (N * p) := Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) (ι N p)

def ψ : C.B N →ₐ[C.κ] LC C.κ N := (C.Φ 0).comp (C.mapι)

theorem ψ_apply (z : C.B N) : C.ψ z = C.Φ 0 (C.mapι z) := rfl

theorem ψ_tmul (x : C.κ) (b : ↥(chartAlgFin N p)) :
    C.ψ (x ⊗ₜ[ℤp] b) = algebraMap C.κ (LC C.κ N) x * C.r 0 (ι N p b) := by
  rw [ψ_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Φ_tmul]

theorem ψ_one_j : C.ψ (1 ⊗ₜ[ℤp] jChartFin N p) = jt C.κ N := by
  rw [ψ_tmul, map_one, one_mul, ι_jChartFin, r_zero_j]

theorem ψ_fB (Q : C.κ[X]) : C.ψ (C.fB N Q) = Polynomial.aeval (jt C.κ N) Q := by
  show C.ψ (Polynomial.aeval _ Q) = _
  rw [← Polynomial.aeval_algHom_apply, ψ_one_j]

theorem ψ_mem_chartRing (z : C.B N) : C.ψ z ∈ CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)) :=
  C.Φ_mem_chartRing 0 _

theorem exists_eFin : ∃ eFin : C.B N ≃ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N))),
    ((eFin ((1 : C.κ) ⊗ₜ[ℤp] jChartFin N p) : ↥(CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)))) :
      LC C.κ N) = jt C.κ N :=
  (exists_algEquiv_residueField_tensor_chartAlg_chartRing N p C.hpN C.A C.hA C.ρ C.hρ).1

scoped instance isDomain_B : IsDomain (C.B N) := by
  obtain ⟨eFin, -⟩ := C.exists_eFin
  exact MulEquiv.isDomain _ eFin.toMulEquiv

theorem ψ_injective : Function.Injective C.ψ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  letI : Algebra C.κ[X] (C.B N) := (C.fB N).toAlgebra
  haveI : Algebra.IsIntegral C.κ[X] (C.B N) := ⟨fun z => C.isIntegralElem_B N z⟩
  refine Ideal.eq_bot_of_comap_eq_bot (R := C.κ[X]) ?_
  refine (Submodule.eq_bot_iff _).mpr fun Q hQ => ?_
  rw [Ideal.mem_comap, RingHom.algebraMap_toAlgebra, RingHom.mem_ker] at hQ
  replace hQ : C.ψ (C.fB N Q) = 0 := hQ
  rw [ψ_fB] at hQ
  have ht : Transcendental C.κ (jt C.κ N) := by
    have := C.transcendental_r_j 0
    rwa [r_zero_j] at this
  exact (transcendental_iff.mp ht) Q hQ

theorem jtd_mem_range (d : ℕ) [NeZero d] (hd : d ∣ N) (hmem : qExpand C.κ d (jqModC C.κ) ∈ modularFunctionFieldFullC C.κ N) :
    (⟨qExpand C.κ d (jqModC C.κ), hmem⟩ : LC C.κ N) ∈ Set.range C.ψ := by
  refine ⟨(1 : C.κ) ⊗ₜ[ℤp] jdO N p d hd, Subtype.ext ?_⟩
  rw [ψ_tmul, map_one, one_mul, coe_r_zero_jd]

theorem adjoin_range_ψ_eq_top : IntermediateField.adjoin C.κ (Set.range C.ψ) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  set E := IntermediateField.adjoin C.κ (Set.range C.ψ)
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap C.κ (LaurentSeries C.κ)) ∪ divisorExpansionsC C.κ N) := hx

  suffices H : ∀ (y : LaurentSeries C.κ), y ∈ Subfield.closure
      (Set.range (algebraMap C.κ (LaurentSeries C.κ)) ∪ divisorExpansionsC C.κ N) →
      ∀ (hy : y ∈ modularFunctionFieldFullC C.κ N), (⟨y, hy⟩ : LC C.κ N) ∈ E from H x hx' hx
  intro y hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
    intro hz'
    rcases hz with ⟨c, rfl⟩ | ⟨d, hne, hdN, rfl⟩
    · have : (⟨algebraMap C.κ (LaurentSeries C.κ) c, hz'⟩ : LC C.κ N) = algebraMap C.κ (LC C.κ N) c :=
        Subtype.ext (show algebraMap C.κ (LaurentSeries C.κ) c =
          ((algebraMap C.κ (LC C.κ N) c : LC C.κ N) : LaurentSeries C.κ) from rfl)
      rw [this]
      exact E.algebraMap_mem c
    · haveI := hne
      exact IntermediateField.subset_adjoin C.κ _ (C.jtd_mem_range d hdN hz')
  | one => intro h1; rw [show (⟨1, h1⟩ : LC C.κ N) = 1 from rfl]; exact one_mem E
  | add a b ha hb iha ihb =>
    intro hab
    have ha' : a ∈ modularFunctionFieldFullC C.κ N := ha
    have hb' : b ∈ modularFunctionFieldFullC C.κ N := hb
    have : (⟨a + b, hab⟩ : LC C.κ N) = ⟨a, ha'⟩ + ⟨b, hb'⟩ := rfl
    rw [this]; exact add_mem (iha ha') (ihb hb')
  | neg a ha iha =>
    intro hna
    have ha' : a ∈ modularFunctionFieldFullC C.κ N := ha
    have : (⟨-a, hna⟩ : LC C.κ N) = -⟨a, ha'⟩ := rfl
    rw [this]; exact neg_mem (iha ha')
  | inv a ha iha =>
    intro hia
    have ha' : a ∈ modularFunctionFieldFullC C.κ N := ha
    have : (⟨a⁻¹, hia⟩ : LC C.κ N) = (⟨a, ha'⟩ : LC C.κ N)⁻¹ := rfl
    rw [this]; exact inv_mem (iha ha')
  | mul a b ha hb iha ihb =>
    intro hab
    have ha' : a ∈ modularFunctionFieldFullC C.κ N := ha
    have hb' : b ∈ modularFunctionFieldFullC C.κ N := hb
    have : (⟨a * b, hab⟩ : LC C.κ N) = ⟨a, ha'⟩ * ⟨b, hb'⟩ := rfl
    rw [this]; exact mul_mem (iha ha') (ihb hb')

theorem exists_eq_div (x : LC C.κ N) : ∃ za zb : C.B N, x = C.ψ za / C.ψ zb := by
  have hx : x ∈ IntermediateField.adjoin C.κ (Set.range C.ψ) := by rw [adjoin_range_ψ_eq_top]; trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hle : Algebra.adjoin C.κ (Set.range C.ψ) ≤ C.ψ.range := Algebra.adjoin_le (fun y hy => C.ψ.mem_range.mpr hy)
  obtain ⟨za, rfl⟩ := (AlgHom.mem_range _).mp (hle ha)
  obtain ⟨zb, rfl⟩ := (AlgHom.mem_range _).mp (hle hb)
  exact ⟨za, zb, rfl⟩

theorem sum_homog {L : Type} [Field L] (c : ℕ → L) (a b : L) (hb : b ≠ 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), c k * a ^ k * b ^ (n - k)) = b ^ n * ∑ k ∈ Finset.range (n + 1), c k * (a / b) ^ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_sub_cancel_left, pow_add, div_pow]
  field_simp

theorem exists_ψ_eq {x : LC C.κ N} (hxD : x ∈ CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N))) :
    ∃ z : C.B N, C.ψ z = x := by
  classical
  obtain ⟨eFin, heFin⟩ := C.exists_eFin

  let α : C.B N →ₐ[C.κ] LC C.κ N := (CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N))).val.comp
    (eFin : C.B N →ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N))))
  have hα_apply : ∀ z, α z = ((eFin z : ↥(CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)))) : LC C.κ N) :=
    fun z => rfl
  have hα_inj : Function.Injective α := fun z₁ z₂ h => eFin.injective (Subtype.ext (by rwa [hα_apply, hα_apply] at h))
  have hα_j : α ((1 : C.κ) ⊗ₜ[ℤp] jChartFin N p) = jt C.κ N := by rw [hα_apply]; exact heFin
  have hα_fB : ∀ Q : C.κ[X], α (C.fB N Q) = Polynomial.aeval (jt C.κ N) Q := by
    intro Q
    show α (Polynomial.aeval _ Q) = _
    rw [← Polynomial.aeval_algHom_apply, hα_j]
  have hα_surj : ∀ y ∈ CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)), ∃ z, α z = y := fun y hy =>
    ⟨eFin.symm ⟨y, hy⟩, by rw [hα_apply, AlgEquiv.apply_symm_apply]⟩

  obtain ⟨za, zb, hx⟩ := C.exists_eq_div x
  by_cases hb : C.ψ zb = 0
  · refine ⟨0, ?_⟩; rw [map_zero, hx, hb, div_zero]
  have hzb : zb ≠ 0 := fun h => hb (by rw [h, map_zero])
  have hb₀ : α zb ≠ 0 := fun h => hzb (hα_inj (by rw [h, map_zero]))

  obtain ⟨P₁, hmonic, hroot⟩ := (CurveModel.mem_chartRing_iff C.κ).mp hxD
  have hlifts : P₁.map (algebraMap _ (LC C.κ N)) ∈
      Polynomial.lifts (Polynomial.aeval (jt C.κ N) : C.κ[X] →ₐ[C.κ] LC C.κ N).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    have hk : ((P₁.coeff k : ↥(Algebra.adjoin C.κ ({jt C.κ N} : Set (LC C.κ N)))) : LC C.κ N) ∈
        (Polynomial.aeval (jt C.κ N) : C.κ[X] →ₐ[C.κ] LC C.κ N).range :=
      (SetLike.ext_iff.mp (Algebra.adjoin_singleton_eq_range_aeval C.κ (jt C.κ N)) _).mp (P₁.coeff k).2
    obtain ⟨Q, hQ⟩ := (AlgHom.mem_range _).mp hk
    exact ⟨Q, hQ⟩
  obtain ⟨P, hPmap, -, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hmonic.map _)
  have hPx : P.eval₂ (Polynomial.aeval (jt C.κ N) : C.κ[X] →ₐ[C.κ] LC C.κ N).toRingHom x = 0 := by
    rw [← Polynomial.eval_map, hPmap, Polynomial.eval_map]; exact hroot

  set n := P.natDegree with hn
  set S : C.B N := ∑ k ∈ Finset.range (n + 1), C.fB N (P.coeff k) * za ^ k * zb ^ (n - k) with hS
  have hψS : C.ψ S = 0 := by
    rw [hS, map_sum]
    simp only [map_mul, map_pow, ψ_fB]
    rw [sum_homog (fun k => Polynomial.aeval (jt C.κ N) (P.coeff k)) _ _ hb, ← hx]
    have : (∑ k ∈ Finset.range (n + 1), (Polynomial.aeval (jt C.κ N)) (P.coeff k) * x ^ k) =
        P.eval₂ (Polynomial.aeval (jt C.κ N) : C.κ[X] →ₐ[C.κ] LC C.κ N).toRingHom x := by
      rw [Polynomial.eval₂_eq_sum_range]; rfl
    rw [this, hPx, mul_zero]
  have hS0 : S = 0 := C.ψ_injective (by rw [hψS, map_zero])

  have hαS : (∑ k ∈ Finset.range (n + 1), (Polynomial.aeval (jt C.κ N)) (P.coeff k) * α za ^ k * α zb ^ (n - k)) = 0 := by
    have := congrArg α hS0
    rw [map_zero, hS, map_sum] at this
    simpa only [map_mul, map_pow, hα_fB] using this
  rw [sum_homog (fun k => Polynomial.aeval (jt C.κ N) (P.coeff k)) _ _ hb₀] at hαS
  have hy : P.eval₂ (Polynomial.aeval (jt C.κ N) : C.κ[X] →ₐ[C.κ] LC C.κ N).toRingHom (α za / α zb) = 0 := by
    rw [Polynomial.eval₂_eq_sum_range]
    exact (mul_eq_zero.mp hαS).resolve_left (pow_ne_zero _ hb₀)

  have hyD : α za / α zb ∈ CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N)) := by
    rw [CurveModel.mem_chartRing_iff]
    exact C.isIntegral_adjoin_of_eval₂ (jt C.κ N) (jt C.κ N) _ (Algebra.self_mem_adjoin_singleton _ _) P hPmonic hy
  obtain ⟨zy, hzy⟩ := hα_surj _ hyD
  have hza : za = zb * zy := by
    apply hα_inj
    rw [map_mul, hzy, ← mul_div_assoc, mul_div_cancel_left₀ _ hb₀]
  refine ⟨zy, ?_⟩
  rw [hx, hza, map_mul, mul_div_cancel_left₀ _ hb]

def ψEquiv : C.B N ≃ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N))) :=
  AlgEquiv.ofBijective (C.ψ.codRestrict _ C.ψ_mem_chartRing)
    ⟨fun z₁ z₂ h => C.ψ_injective (congrArg Subtype.val h :),
     fun ⟨x, hx⟩ => by obtain ⟨z, hz⟩ := C.exists_ψ_eq hx; exact ⟨z, Subtype.ext hz⟩⟩

theorem coe_ψEquiv (z : C.B N) : (C.ψEquiv z : LC C.κ N) = C.ψ z := rfl

def ΦD (i : Fin 2) : C.B (N * p) →ₐ[C.κ] ↥(CurveModel.chartRing C.κ ({jt C.κ N} : Set (LC C.κ N))) :=
  (C.Φ i).codRestrict _ (C.Φ_mem_chartRing i)

theorem coe_ΦD (i : Fin 2) (z : C.B (N * p)) : (C.ΦD i z : LC C.κ N) = C.Φ i z := rfl

def σ (i : Fin 2) : C.B (N * p) →ₐ[C.κ] C.B N := (C.ψEquiv.symm : _ →ₐ[C.κ] C.B N).comp (C.ΦD i)

theorem σ_apply (i : Fin 2) (z : C.B (N * p)) : C.σ i z = C.ψEquiv.symm (C.ΦD i z) := rfl

theorem ψ_σ (i : Fin 2) (z : C.B (N * p)) : C.ψ (C.σ i z) = C.Φ i z := by
  rw [σ_apply, ← coe_ψEquiv, AlgEquiv.apply_symm_apply, coe_ΦD]

theorem σ_eq_iff (i : Fin 2) (z : C.B (N * p)) (y : C.B N) : C.σ i z = y ↔ C.Φ i z = C.ψ y := by
  constructor
  · rintro rfl; rw [ψ_σ]
  · intro h; exact C.ψ_injective (by rw [ψ_σ, h])

theorem σ_zero_mapι (z : C.B N) : C.σ 0 (C.mapι z) = z := (C.σ_eq_iff 0 _ _).mpr rfl

theorem σ_one_eq (z : C.B (N * p)) : C.σ 1 z = C.σ 0 (C.mapw z) := by
  rw [σ_eq_iff, ψ_σ, Φ_one_eq_Φ_zero_mapw]

theorem map_comp_eq (z : C.B N) :
    Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) ((C.w : _ →ₐ[ℤp] _).comp (ι N p)) z = C.mapw (C.mapι z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem σ_one_map (z : C.B N) :
    C.σ 1 (Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) ((C.w : _ →ₐ[ℤp] _).comp (ι N p)) z) = z := by
  rw [map_comp_eq, σ_one_eq, mapw_mapw, σ_zero_mapι]

theorem ker_σ (i : Fin 2) : RingHom.ker (C.σ i) = RingHom.ker (C.Φ i) := by
  ext z
  rw [RingHom.mem_ker, RingHom.mem_ker, σ_eq_iff, map_zero]

theorem ker_σ_mem_minimalPrimes (i : Fin 2) : RingHom.ker (C.σ i) ∈ minimalPrimes (C.B (N * p)) := by
  rw [ker_σ]; exact C.ker_Φ_mem_minimalPrimes i

theorem σ_zero_j : C.σ 0 ((1 : C.κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = (1 : C.κ) ⊗ₜ[ℤp] jChartFin N p := by
  rw [σ_eq_iff, Φ_one_tmul, r_zero_j, ψ_one_j]

theorem σ_one_j : C.σ 1 ((1 : C.κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = ((1 : C.κ) ⊗ₜ[ℤp] jChartFin N p) ^ p := by
  rw [σ_eq_iff, Φ_one_tmul, r_one_j, map_pow, ψ_one_j]

theorem u_eq (u : ↥(chartAlgFin (N * p) p))
    (hu : (u : FF (N * p)) = atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p) :
    u = C.w (jChartFin (N * p) p) - jChartFin (N * p) p ^ p := by
  apply Subtype.ext
  rw [hu, Subalgebra.coe_sub, Subalgebra.coe_pow, C.hw, coe_jChartFin]

theorem σ_zero_u (u : ↥(chartAlgFin (N * p) p))
    (hu : (u : FF (N * p)) = atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p) :
    C.σ 0 ((1 : C.κ) ⊗ₜ[ℤp] u) = 0 := by
  rw [← RingHom.mem_ker, ker_σ, RingHom.mem_ker, Φ_one_tmul, C.u_eq u hu, map_sub, map_pow, r_zero_wj,
    r_zero_j, sub_self]

theorem σ_one_u (u : ↥(chartAlgFin (N * p) p))
    (hu : (u : FF (N * p)) = atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p) :
    C.σ 1 ((1 : C.κ) ⊗ₜ[ℤp] u) ≠ 0 := by
  rw [Ne, ← RingHom.mem_ker, ker_σ, RingHom.mem_ker, Φ_one_tmul, C.u_eq u hu, map_sub, map_pow, r_one_wj,
    r_one_j, sub_eq_zero, ← pow_mul]
  intro h
  have ht : Transcendental C.κ (jt C.κ N) := by
    have := C.transcendental_r_j 0
    rwa [r_zero_j] at this
  have hp : 1 < p * p := lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_mul_self p)
  have h0 := (transcendental_iff.mp ht) (X - X ^ (p * p))
    (by rw [map_sub, map_pow, Polynomial.aeval_X, ← h, sub_self])
  have := congrArg (fun Q : C.κ[X] => Q.coeff 1) h0
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at this
  rw [if_neg (Nat.ne_of_lt hp)] at this
  norm_num at this

theorem ker_ne : RingHom.ker (C.σ 0) ≠ RingHom.ker (C.σ 1) := by
  let u : ↥(chartAlgFin (N * p) p) := C.w (jChartFin (N * p) p) - jChartFin (N * p) p ^ p
  have hu : (u : FF (N * p)) = atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p := by
    show ((C.w (jChartFin (N * p) p) - jChartFin (N * p) p ^ p : ↥(chartAlgFin (N * p) p)) : FF (N * p)) = _
    rw [Subalgebra.coe_sub, Subalgebra.coe_pow, C.hw, coe_jChartFin]
  intro h
  have h0 : ((1 : C.κ) ⊗ₜ[ℤp] u) ∈ RingHom.ker (C.σ 0) := C.σ_zero_u u hu
  rw [h] at h0
  exact C.σ_one_u u hu h0

theorem main :
    ∃ σ : Fin 2 → (C.κ ⊗[ℤp] ↥(chartAlgFin (N * p) p) →ₐ[C.κ] C.κ ⊗[ℤp] ↥(chartAlgFin N p)),
      (∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) (ι N p) z) = z) ∧
      (∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) (C.w : _ →ₐ[ℤp] _) z)) ∧
      (∀ z, σ 1 (Algebra.TensorProduct.map (AlgHom.id C.κ C.κ) ((C.w : _ →ₐ[ℤp] _).comp (ι N p)) z) = z) ∧
      (∀ i, RingHom.ker (σ i) ∈ minimalPrimes (C.κ ⊗[ℤp] ↥(chartAlgFin (N * p) p))) ∧
      RingHom.ker (σ 0) ≠ RingHom.ker (σ 1) ∧
      σ 0 ((1 : C.κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = (1 : C.κ) ⊗ₜ[ℤp] jChartFin N p ∧
      σ 1 ((1 : C.κ) ⊗ₜ[ℤp] jChartFin (N * p) p) = ((1 : C.κ) ⊗ₜ[ℤp] jChartFin N p) ^ p ∧
      ∀ u : ↥(chartAlgFin (N * p) p),
        (u : FF (N * p)) = atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p →
        σ 0 ((1 : C.κ) ⊗ₜ[ℤp] u) = 0 ∧ σ 1 ((1 : C.κ) ⊗ₜ[ℤp] u) ≠ 0 :=
  ⟨C.σ, C.σ_zero_mapι, C.σ_one_eq, C.σ_one_map, C.ker_σ_mem_minimalPrimes, C.ker_ne, C.σ_zero_j, C.σ_one_j,
    fun u hu => ⟨C.σ_zero_u u hu, C.σ_one_u u hu⟩⟩

end Ctx
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd.IgusaFibreComponents.Ctx"

end IgusaFibreComponents
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd.IgusaFibreComponents.Ctx P2MW.S_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd.IgusaFibreComponents"

open IgusaFibreComponents in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :
    letI := ((residue ↥A).comp ρ).toAlgebra
    ∃ (ι : ↥(chartAlgFin N p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))
      (w : ↥(chartAlgFin (N * p) p) ≃ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)),

      (∀ b, (((ι b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      (∀ b, ((w b : ↥(chartAlgFin (N * p) p)) : ↥(modularFunctionFieldFull (N * p))) =
        atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p)))) ∧
      ∃ σ : Fin 2 → (ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[ResidueField ↥A]
          ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin N p)),

        (∀ z, σ 0 (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥A) (ResidueField ↥A)) ι z) = z) ∧

        (∀ z, σ 1 z = σ 0 (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥A) (ResidueField ↥A))
          (w : _ →ₐ[↥(GaloisRep.ratLocalizedAt p)] _) z)) ∧
        (∀ z, σ 1 (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥A) (ResidueField ↥A))
          ((w : _ →ₐ[↥(GaloisRep.ratLocalizedAt p)] _).comp ι) z) = z) ∧

        (∀ i, RingHom.ker (σ i) ∈
          minimalPrimes (ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))) ∧
        RingHom.ker (σ 0) ≠ RingHom.ker (σ 1) ∧

        σ 0 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (N * p) p) =
          (1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p ∧
        σ 1 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin (N * p) p) =
          ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] jChartFin N p) ^ p ∧

        ∀ u : ↥(chartAlgFin (N * p) p),
          (u : ↥(modularFunctionFieldFull (N * p))) =
            atkinLehnerInvolutionFull N p (jFull (N * p)) - jFull (N * p) ^ p →
          σ 0 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] u) = 0 ∧
          σ 1 ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] u) ≠ 0 := by
  obtain ⟨R, -, h1b, h2, h2b, -, ⟨hj, hres0, hres1, -, -, -⟩, -⟩ :=
    exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd N p hpN A hA
  obtain ⟨w, hw, hww⟩ := exists_algEquiv_chartAlgFin_mul_eq_atkinLehnerInvolutionFull N p hpN
  let C : Ctx N p :=
    { A := A, hA := hA, charP := inferInstance, algClosed := inferInstance, R := R, h1b := h1b, h2 := h2,
      h2b := h2b, hj := hj, hres0 := hres0, hres1 := hres1, ρ := ρ, hρ := hρ, w := w, hw := hw, hww := hww,
      hpN := hpN }
  refine ⟨ι N p, w, coe_coe_ι N p, hw, ?_⟩
  exact C.main

end
end S_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_retraction_pair_residueField_tensor_chartAlgFin_mul_of_not_dvd (solution)
