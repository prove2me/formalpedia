-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.exists_heckeRowSums_and_adjointPair_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0e374cd5-cc80-5615-8f0e-498f7bc018ea

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_PlaceWidthChar
import Theorems.Thm_ModularCurve_SSLevelDatum_heckeLaws_of_prime_ne_of_not_dvd
import Theorems.Thm_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_self
import Theorems.Thm_ModularCurve_SSLevelDatum_edgeHecke_apply_and_vertexHecke_apply_of_ne
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaC_residueField_eq_add_one
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_comm_of_exchange
import Theorems.Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
import Theorems.Thm_ModularCurve_placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime
import Theorems.Thm_ModularCurve_one_le_placeWidthChar_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ValuationSubring.instIsAlgClosedResidueField GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_jqNGen PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve CerednikDrinfeld"

namespace ModularCurve
p2m_export "ModularCurve" "levelAlphaC coe_levelAlphaC levelBetaC coe_levelBetaC SSLevelDatum charLDegeneracyRoof heckeAlphaC heckeBetaC HeckeAlphaCIntegral HeckeBetaCIntegral frobOnPlacesGeomLevel modularFunctionFieldC ModularPolynomialData KroneckerCongruence placeWidth ssPlaces characterLattice HeckeRowSums placeWidthChar placeWidthChar_of_five_le SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_mem_ssPlaces frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed hasPrincipalDivisors_charLDegeneracyRoof finiteAlong_heckeBetaC finiteAlong_heckeAlphaC separableAlong_heckeAlphaC_heckeBetaC restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces finrankAlong_heckeAlphaC_residueField_eq_add_one exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime one_le_placeWidthChar_of_mem_ssPlaces ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong placeRamificationJ_dvd_jWidth_of_mem_ssPlaces"
namespace SSLevelDatum
p2m_export "ModularCurve.SSLevelDatum" "degeneracyData edgeHecke vertexHecke HeckeLaws sndIntegral legsIntegral mem_s frobData mem_M fstIntegral kronecker heckeLaws_of_prime_ne_of_not_dvd edgeHecke_apply_and_vertexHecke_apply_self edgeHecke_apply_and_vertexHecke_apply_of_ne degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec"
namespace IdentEngines
p2m_open "ModularCurve.SSLevelDatum ModularCurve"

section Generic

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

theorem jointDelta_apply_eq_mulVec (D : DegeneracyData E V) (i : Fin 2) (z : E → ℤ) :
    jointDelta D i z = (degeneracyMatrix (![D.a, D.b] i)).mulVec z := by
  fin_cases i <;> rfl

theorem degeneracyMatrix_mulVec_apply (f : E → V) (y : E → ℤ) (v : V) :
    (degeneracyMatrix f).mulVec y v = ∑ e, if f e = v then y e else 0 := by
  simp only [Matrix.mulVec, dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]

theorem sum_mul_degeneracyMatrix_mulVec_mul (f : E → V) (c : V → ℤ) (y : E → ℤ) (x : V → ℤ) :
    ∑ v, c v * (degeneracyMatrix f).mulVec y v * x v = ∑ e, c (f e) * y e * x (f e) := by
  simp only [degeneracyMatrix_mulVec_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_eq_single (f e)]
  · simp
  · intro v _ hv
    rw [if_neg (Ne.symm hv)]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mem_characterLattice_iff_mulVec (f : E → V) (y : E → ℤ) :
    y ∈ characterLattice E ↔ (degeneracyMatrix f).mulVec y ∈ characterLattice V := by
  have h := degreeOn_pushforward f y
  simp only [pushforward, Matrix.mulVecLin_apply] at h
  simp only [characterLattice, LinearMap.mem_ker, h]

theorem matrix_eq_of_forall_mulVec_eq {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A B : Matrix m n ℤ} (h : ∀ x, A.mulVec x = B.mulVec x) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

end Generic

theorem deg_eq_one_of_isRational {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    (hv : v.IsRational) : v.deg = 1 := by
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    ⟨(algebraMap K v.ResidueField).injective, hv⟩
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

theorem degree_eq_sum_of_forall_isRational {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F)
    (h : ∀ v ∈ D.support, v.IsRational) : Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [AddMonoidHom.mulRight_apply, deg_eq_one_of_isRational (h v hv), Nat.cast_one, mul_one]

scoped instance instIsAlgClosedResidueField (A : ValuationSubring (AlgebraicClosure ℚ)) :
    IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
  ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

theorem liesOverPrime_of_charP (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ)
    [CharP (IsLocalRing.ResidueField ↥A) q] : A.LiesOverPrime q := by
  have h : IsLocalRing.residue ↥A (q : ↥A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ q
  rw [IsLocalRing.residue_eq_zero_iff] at h
  have h' : ((q : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr h
  simpa [ValuationSubring.LiesOverPrime] using h'

section Frame

variable (q' : ℕ) [Fact q'.Prime] (hq5 : 5 ≤ q') (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']

theorem natCast_ne_zero_of_not_dvd (n : ℕ) (h : ¬ q' ∣ n) : (n : (IsLocalRing.ResidueField ↥A)) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) q' n]
  exact h

theorem natCast_ne_zero_of_prime_ne (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq' : ℓ ≠ q') : (ℓ : (IsLocalRing.ResidueField ↥A)) ≠ 0 :=
  natCast_ne_zero_of_not_dvd q' A ℓ (fun h => hℓq' ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).1 h).symm)

theorem hasPrincipalDivisors_roof (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓq' : ℓ ≠ q')
    (hq'N : ¬ q' ∣ N) : HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ) :=
  hasPrincipalDivisors_charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ (natCast_ne_zero_of_not_dvd q' A N hq'N)
    (natCast_ne_zero_of_prime_ne q' A ℓ Fact.out hℓq')

include hq5 in

theorem cast_toPNat'_placeWidth (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) (hv : v ∈ ssPlaces q' N (IsLocalRing.ResidueField ↥A)) :
    ((Nat.toPNat' (placeWidth N v) : ℕ) : ℤ) = (placeWidthChar q' N v : ℤ) := by
  have h1 : 1 ≤ placeWidthChar q' N v := one_le_placeWidthChar_of_mem_ssPlaces hq'N hv
  have h2 : placeWidthChar q' N v = placeWidth N v := placeWidthChar_of_five_le hq5 N v
  rw [h2] at h1 ⊢
  rw [Nat.toPNat'_coe, if_pos (show 0 < placeWidth N v by omega)]

include hq5 in
theorem cast_toPNat'_placeWidth' (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) (hv : v ∈ ssPlaces q' N (IsLocalRing.ResidueField ↥A)) :
    ((Nat.toPNat' (placeWidth N v) : ℕ) : ℤ) = (placeWidth N v : ℤ) := by
  rw [cast_toPNat'_placeWidth q' hq5 A N hq'N v hv, placeWidthChar_of_five_le hq5 N v]

noncomputable def colsum (N B : ℕ) [NeZero N] (ℓ : Nat.Primes) : ℤ :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  if (ℓ : ℕ) ∣ B then
    (if (ℓ : ℕ) = q' then 1 else (finrankAlong (IsLocalRing.ResidueField ↥A) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) : ℤ))
  else ((ℓ : ℕ) : ℤ) + 1

theorem colsum_of_not_dvd (N B : ℕ) [NeZero N] (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ B) :
    colsum q' A N B ℓ = ((ℓ : ℕ) : ℤ) + 1 := by
  simp only [colsum, if_neg hℓ]

section Frob

variable (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N) (data : ModularPolynomialData q') (hKr : KroneckerCongruence q' data)

include hq'N in
theorem frob_mem (w : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) (hw : w ∈ ssPlaces q' N (IsLocalRing.ResidueField ↥A)) :
    frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr w ∈ ssPlaces q' N (IsLocalRing.ResidueField ↥A) := by
  rw [← arithFrobC_smul_eq_frobOnPlacesGeomLevel q' (IsLocalRing.ResidueField ↥A) N data hKr w]
  exact arithFrobC_smul_mem_ssPlaces q' N (IsLocalRing.ResidueField ↥A) w hw

noncomputable def frobPerm : Equiv.Perm ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) :=
  Function.Involutive.toPerm
    (fun x => ⟨frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr x.1, frob_mem q' A N hq'N data hKr x.1 x.2⟩)
    (fun x => Subtype.ext
      (frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed (IsLocalRing.ResidueField ↥A) N hq'N
        data hKr x.1 x.2))

theorem frobPerm_apply_coe (x : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))) :
    ((frobPerm q' A N hq'N data hKr x : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))) : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) =
      frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr x.1 :=
  rfl

open Classical in
include hq'N in

theorem exists_perm_of_frob [DecidableEq ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))]
    (T : Matrix ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) ℤ)
    (hT : ∀ y x : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)),
      T y x = if frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr x.1 = y.1 then 1 else 0) :
    ∃ σ : Equiv.Perm ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)), ∀ i j, T i j = if i = σ j then 1 else 0 := by
  refine ⟨frobPerm q' A N hq'N data hKr, fun i j => ?_⟩
  rw [hT i j]
  have : (frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr j.1 = i.1) ↔ (i = frobPerm q' A N hq'N data hKr j) := by
    rw [Subtype.ext_iff, frobPerm_apply_coe, eq_comm]
  by_cases h : frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr j.1 = i.1
  · rw [if_pos h, if_pos (this.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

open Classical in
include hq'N in

theorem heckeRowSums_transpose_of_frob [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))]
    (T : Matrix ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) ℤ)
    (hT : ∀ y x : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)),
      T y x = if frobOnPlacesGeomLevel (IsLocalRing.ResidueField ↥A) N data hKr x.1 = y.1 then 1 else 0) :
    HeckeRowSums T.transpose 1 := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_frob q' A N hq'N data hKr T hT
  intro x
  simp only [Matrix.transpose_apply, hσ]
  rw [Finset.sum_eq_single (σ x)]
  · simp
  · intro y _ hy
    rw [if_neg hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Frob

section Colsum

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓq' : ℓ ≠ q') (hq'N : ¬ q' ∣ N)

set_option maxHeartbeats 3200000 in
include hℓq' hq'N in

theorem sum_ssPlaces_correspondence_heckeBetaC_heckeAlphaC
    [HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)]
    (hα : HeckeAlphaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ) (hβ : HeckeBetaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ)
    [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))] (x : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))) :
    ∑ y : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)),
        Divisor.correspondence (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ hα (Finsupp.single x.1 1) y.1 =
      (finrankAlong (IsLocalRing.ResidueField ↥A) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) : ℤ) := by
  classical
  have hq'Nℓ : ¬ q' ∣ N * ℓ := by
    intro h
    rcases (Fact.out : q'.Prime).dvd_mul.1 h with h | h
    · exact hq'N h
    · exact hℓq' ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h).symm
  have hFI : FundamentalIdentityAlong (IsLocalRing.ResidueField ↥A) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ :=
    AlgebraicCurve.fundamentalIdentityAlong (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ (finiteAlong_heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ)
      (separableAlong_heckeAlphaC_heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ hq'Nℓ).2
  set D : Divisor (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N) :=
    Divisor.correspondence (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ hα (Finsupp.single x.1 1) with hD

  have hsupp : ∀ y : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N), y ∉ ssPlaces q' N (IsLocalRing.ResidueField ↥A) → D y = 0 := by
    intro y hy
    rw [hD, Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, if_neg]
    intro hWy
    apply hy
    rw [← hWy]
    refine restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces q' N ℓ Fact.out hℓq'
      hq'N hα hβ W ?_
    rw [Place.mem_fiberAlong.1 hW]
    exact x.2
  have hsub : D.support ⊆ (ssPlaces q' N (IsLocalRing.ResidueField ↥A)).toFinset := by
    intro y hy
    rw [Set.mem_toFinset]
    by_contra hy'
    exact (Finsupp.mem_support_iff.1 hy) (hsupp y hy')

  have hsum : ∑ y : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)), D y.1 = ∑ y ∈ D.support, D y := by
    rw [← Finset.sum_subtype (ssPlaces q' N (IsLocalRing.ResidueField ↥A)).toFinset (fun y => Set.mem_toFinset) (fun y => D y)]
    exact (Finset.sum_subset hsub (fun y _ hy => Finsupp.notMem_support_iff.1 hy)).symm

  have hdeg : Divisor.degree D = ∑ y ∈ D.support, D y := by
    refine degree_eq_sum_of_forall_isRational D fun y hy => ?_
    have hy' : y ∈ ssPlaces q' N (IsLocalRing.ResidueField ↥A) := Set.mem_toFinset.1 (hsub hy)
    exact hy'.1
  rw [hsum, ← hdeg, hD, Divisor.degree_correspondence _ _ _ _ hFI, Divisor.degree_single,
    deg_eq_one_of_isRational x.2.1]
  simp

set_option maxHeartbeats 3200000 in
include hℓq' hq'N in

theorem correspondence_heckeBetaC_heckeAlphaC_eq_of_not_dvd (hℓN : ¬ ℓ ∣ N)
    [HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)]
    (hα : HeckeAlphaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ) (hβ : HeckeBetaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ) :
    Divisor.correspondence (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ hα =
      Divisor.correspondence (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) hα hβ := by
  obtain ⟨w, h1, h2⟩ :=
    (exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap (IsLocalRing.ResidueField ↥A) q' N hq'N ℓ hℓq').2.2 hℓN
  have hgs : Function.Surjective (w : ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ) →ₐ[(IsLocalRing.ResidueField ↥A)] ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)) :=
    fun y => ⟨w.symm y, w.apply_symm_apply y⟩
  have hg : (w : ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ) →ₐ[(IsLocalRing.ResidueField ↥A)] ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ hgs
  exact Divisor.correspondence_comm_of_exchange (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ hα
    (w : ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ) →ₐ[(IsLocalRing.ResidueField ↥A)] ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)) hg hgs
    (AlgHom.ext h2) (AlgHom.ext h1)

include hℓq' hq'N in

theorem finrankAlong_heckeBetaC_eq_add_one (hℓN : ¬ ℓ ∣ N)
    [HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)]
    (hα : HeckeAlphaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ) (hβ : HeckeBetaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ)
    (x : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) (hx : x ∈ ssPlaces q' N (IsLocalRing.ResidueField ↥A)) :
    (finrankAlong (IsLocalRing.ResidueField ↥A) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) : ℤ) = (ℓ : ℤ) + 1 := by
  have hq'Nℓ : ¬ q' ∣ N * ℓ := by
    intro h
    rcases (Fact.out : q'.Prime).dvd_mul.1 h with h | h
    · exact hq'N h
    · exact hℓq' ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h).symm
  have hFIβ : FundamentalIdentityAlong (IsLocalRing.ResidueField ↥A) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ :=
    AlgebraicCurve.fundamentalIdentityAlong (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ (finiteAlong_heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ)
      (separableAlong_heckeAlphaC_heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ hq'Nℓ).2
  have hFIα : FundamentalIdentityAlong (IsLocalRing.ResidueField ↥A) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hα :=
    AlgebraicCurve.fundamentalIdentityAlong (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hα (finiteAlong_heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ)
      (separableAlong_heckeAlphaC_heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ hq'Nℓ).1
  have hdegβ := Divisor.degree_correspondence (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ hα hFIβ
    (Finsupp.single x 1)
  have hdegα := Divisor.degree_correspondence (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) hα hβ hFIα
    (Finsupp.single x 1)
  rw [correspondence_heckeBetaC_heckeAlphaC_eq_of_not_dvd q' A N ℓ hℓq' hq'N hℓN hα hβ, hdegα,
    Divisor.degree_single, deg_eq_one_of_isRational hx.1] at hdegβ
  have hα1 : finrankAlong (IsLocalRing.ResidueField ↥A) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) = ℓ + 1 :=
    finrankAlong_heckeAlphaC_residueField_eq_add_one N q' Fact.out hq'N A (liesOverPrime_of_charP A q') ℓ hℓq'
      hℓN
  have : (finrankAlong (IsLocalRing.ResidueField ↥A) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) : ℤ) = (finrankAlong (IsLocalRing.ResidueField ↥A) (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) : ℤ) := by
    simpa using hdegβ
  rw [← this, hα1]
  push_cast
  ring

end Colsum

section Symm

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ] [Fact ℓ.Prime] (hℓq' : ℓ ≠ q') (hq'N : ¬ q' ∣ N) (hℓN : ¬ ℓ ∣ N)

include hq5 hℓq' hq'N hℓN in

theorem toPNat'_placeWidth_mul_comm
    [HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) ↥(charLDegeneracyRoof (IsLocalRing.ResidueField ↥A) N ℓ)]
    (hα : HeckeAlphaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ) (hβ : HeckeBetaCIntegral (IsLocalRing.ResidueField ↥A) N ℓ)
    (T : Matrix ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)) ℤ)
    (hT : ∀ y x : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A)), T y x =
      Divisor.correspondence (heckeBetaC (IsLocalRing.ResidueField ↥A) N ℓ) (heckeAlphaC (IsLocalRing.ResidueField ↥A) N ℓ) hβ hα (Finsupp.single x.1 1) y.1)
    (i j : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A))) :
    ((Nat.toPNat' (placeWidth N i.1) : ℕ) : ℤ) * T i j = ((Nat.toPNat' (placeWidth N j.1) : ℕ) : ℤ) * T j i := by
  rw [cast_toPNat'_placeWidth q' hq5 A N hq'N i.1 i.2, cast_toPNat'_placeWidth q' hq5 A N hq'N j.1 j.2, hT, hT]
  have h1 := placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime N ℓ q' Fact.out
    hℓq' hq'N hℓN hα hβ j.1 i.1
  have h2 := placeWidthChar_mul_correspondence_heckeAlphaC_heckeBetaC_single_comm_of_prime N ℓ q' Fact.out
    hℓq' hq'N hℓN hα hβ j.1 i.1
  have h3 := placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime N ℓ q' Fact.out
    hℓq' hq'N hℓN hα hβ i.1 j.1
  rw [h1, h2, ← h3]

end Symm

end Frame

section Datum

variable (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)

include hs hsq' hq'M in
theorem not_q'_dvd_Ms : ¬ q' ∣ M * s := by
  intro h
  rcases (Fact.out : q'.Prime).dvd_mul.1 h with h | h
  · exact hq'M h
  · exact hsq' ((Nat.prime_dvd_prime_iff_eq Fact.out hs).1 h).symm

noncomputable def levelLeg (i : Fin 2) :
    ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) M) →ₐ[(IsLocalRing.ResidueField ↥A)] ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) (M * s)) :=
  ![levelAlphaC (IsLocalRing.ResidueField ↥A) M s X.mem_M, levelBetaC (IsLocalRing.ResidueField ↥A) M s X.mem_s] i

theorem levelLeg_integral (i : Fin 2) : (levelLeg M s q' A X i).toRingHom.IsIntegral := by
  fin_cases i
  · exact X.fstIntegral
  · exact X.sndIntegral

theorem coe_degeneracyMap_eq_restrictAlong (i : Fin 2) (e : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))) :
    (((![X.degeneracyData.a, X.degeneracyData.b] i) e : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))) :
        Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) M)) =
      Place.restrictAlong (levelLeg M s q' A X i) (levelLeg_integral M s q' A X i) e.1 := by
  fin_cases i <;> rfl

noncomputable def ramMult (i : Fin 2) (e : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))) : ℤ :=
  (Place.ramificationIndexAlong (levelLeg M s q' A X i) e.1 : ℤ)

noncomputable def padj (i : Fin 2) :
    (↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) →ₗ[ℤ] (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ) where
  toFun x := fun e => ramMult M s q' A X i e * x ((![X.degeneracyData.a, X.degeneracyData.b] i) e)
  map_add' x y := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem padj_apply (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) (e : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))) :
    padj M s q' A X i x e = ramMult M s q' A X i e * x ((![X.degeneracyData.a, X.degeneracyData.b] i) e) :=
  rfl

include hs hq5 hsq' hq'M in

theorem w_mul_ramMult (i : Fin 2) (e : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))) :
    (X.degeneracyData.w e : ℤ) * ramMult M s q' A X i e =
      (Nat.toPNat' (placeWidth M ((![X.degeneracyData.a, X.degeneracyData.b] i) e).1) : ℤ) := by
  have hq'Ms := not_q'_dvd_Ms M s q' hs hsq' hq'M
  have hw : (X.degeneracyData.w e : ℤ) = ((Nat.toPNat' (placeWidth (M * s) e.1) : ℕ) : ℤ) := rfl
  have hmain := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong M s q' hs hsq' hq'M
    (k := (IsLocalRing.ResidueField ↥A)) (levelLeg M s q' A X) (levelLeg_integral M s q' A X)
    (fun x => coe_levelAlphaC (IsLocalRing.ResidueField ↥A) M s X.mem_M x) (fun x => coe_levelBetaC (IsLocalRing.ResidueField ↥A) M s X.mem_s x) i e.1
    (placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq5 hq'Ms e.2)
  rw [hw, cast_toPNat'_placeWidth' q' hq5 A (M * s) hq'Ms e.1 e.2,
    cast_toPNat'_placeWidth' q' hq5 A M hq'M _ ((![X.degeneracyData.a, X.degeneracyData.b] i) e).2,
    coe_degeneracyMap_eq_restrictAlong, ← hmain, ramMult]
  push_cast
  ring

include hs hq5 hsq' hq'M in

theorem hadj (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) (y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ) :
    (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
        (degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
      ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj M s q' A X i x e := by
  rw [sum_mul_degeneracyMatrix_mulVec_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [padj_apply, ← w_mul_ramMult M s q' hs hq5 hsq' hq'M A X i e]
  ring

include hs hq5 hsq' hq'M hsM in

theorem padj_mem_characterLattice (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ)
    (hx : x ∈ characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))) :
    padj M s q' A X i x ∈ characterLattice ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) := by
  have h := (degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec M s q' hs hq5 hsq' hq'M hsM A X
    (padj M s q' A X) (hadj M s q' hs hq5 hsq' hq'M A X)).1 i x
  rw [mem_characterLattice_iff_mulVec (![X.degeneracyData.a, X.degeneracyData.b] i), h]
  exact Submodule.smul_mem _ _ hx

include hsq' hq'M hsM in
theorem heckeLaws : haveI : Fact s.Prime := ⟨hs⟩; X.HeckeLaws :=
  haveI : Fact s.Prime := ⟨hs⟩
  heckeLaws_of_prime_ne_of_not_dvd M s q' hsq' hq'M hsM A X

include hs hsq' hq'M hsM in
theorem commute_edgeHecke (ℓ ℓ' : Nat.Primes) : Commute (X.edgeHecke ℓ) (X.edgeHecke ℓ') :=
  (heckeLaws M s q' hs hsq' hq'M hsM A X).1 ℓ ℓ'

include hs hsq' hq'M hsM in
theorem commute_vertexHecke (ℓ ℓ' : Nat.Primes) : Commute (X.vertexHecke ℓ) (X.vertexHecke ℓ') :=
  (heckeLaws M s q' hs hsq' hq'M hsM A X).2.1 ℓ ℓ'

include hs hsq' hq'M hsM in

theorem degeneracyMatrix_mul_edgeHecke (i : Fin 2) (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ s) :
    degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) * X.edgeHecke ℓ =
      X.vertexHecke ℓ * degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have h := (heckeLaws M s q' hs hsq' hq'M hsM A X).2.2.1 ℓ (by
    rw [Finset.mem_singleton]
    intro e
    exact hℓ (congrArg Subtype.val e)) i
  refine matrix_eq_of_forall_mulVec_eq fun x => ?_
  have hx := h x
  rw [jointDelta_apply_eq_mulVec, jointDelta_apply_eq_mulVec, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply] at hx
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx]

include hs hsq' hq'M hsM in

theorem kernel_stable (x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ)
    (hx : ∀ i : Fin 2, (degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec x = 0)
    (i : Fin 2) :
    (degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec x) = 0 := by
  haveI : Fact s.Prime := ⟨hs⟩
  have h := (heckeLaws M s q' hs hsq' hq'M hsM A X).2.2.2 ⟨s, hs⟩ x (fun j => by
    rw [jointDelta_apply_eq_mulVec]
    exact hx j) i
  rwa [jointDelta_apply_eq_mulVec, Matrix.mulVecLin_apply] at h

theorem dvd_of_eq_q' (ℓ : Nat.Primes) (h : (ℓ : ℕ) = q') : (ℓ : ℕ) ∣ (M * q') * s :=
  h ▸ (dvd_mul_left q' M).mul_right s

include hs hq5 hsq' hq'M in

theorem heckeRowSums_edgeHecke_transpose (ℓ : Nat.Primes) :
    HeckeRowSums (X.edgeHecke ℓ).transpose (colsum q' A (M * s) ((M * q') * s) ℓ) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hq'Ms := not_q'_dvd_Ms M s q' hs hsq' hq'M
  by_cases h : (ℓ : ℕ) = q'
  · have e : colsum q' A (M * s) ((M * q') * s) ℓ = 1 := by
      simp only [colsum, if_pos (dvd_of_eq_q' M s q' ℓ h), if_pos h]
    rw [e]
    exact heckeRowSums_transpose_of_frob q' A (M * s) hq'Ms X.frobData X.kronecker _
      (edgeHecke_apply_and_vertexHecke_apply_self X ℓ h).1
  · haveI := hasPrincipalDivisors_roof q' A (M * s) ℓ h hq'Ms
    intro x
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_congr rfl fun y _ => (edgeHecke_apply_and_vertexHecke_apply_of_ne X ℓ h).1 y x,
      sum_ssPlaces_correspondence_heckeBetaC_heckeAlphaC q' A (M * s) ℓ h hq'Ms
        (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 x]
    by_cases hd : (ℓ : ℕ) ∣ (M * q') * s
    · simp only [colsum, if_pos hd, if_neg h]
    · rw [colsum_of_not_dvd q' A (M * s) ((M * q') * s) ℓ hd]
      have hℓMs : ¬ (ℓ : ℕ) ∣ M * s := fun h' => hd (h'.trans ⟨q', by ring⟩)
      exact finrankAlong_heckeBetaC_eq_add_one q' A (M * s) ℓ h hq'Ms hℓMs
        (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 x.1 x.2

include hq5 hq'M in

theorem heckeRowSums_vertexHecke_transpose (ℓ : Nat.Primes) :
    HeckeRowSums (X.vertexHecke ℓ).transpose (colsum q' A M (M * q') ℓ) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  by_cases h : (ℓ : ℕ) = q'
  · have e : colsum q' A M (M * q') ℓ = 1 := by
      simp only [colsum, if_pos (show (ℓ : ℕ) ∣ M * q' from h ▸ dvd_mul_left q' M), if_pos h]
    rw [e]
    exact heckeRowSums_transpose_of_frob q' A M hq'M X.frobData X.kronecker _
      (edgeHecke_apply_and_vertexHecke_apply_self X ℓ h).2
  · haveI := hasPrincipalDivisors_roof q' A M ℓ h hq'M
    intro x
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_congr rfl fun y _ => (edgeHecke_apply_and_vertexHecke_apply_of_ne X ℓ h).2 y x,
      sum_ssPlaces_correspondence_heckeBetaC_heckeAlphaC q' A M ℓ h hq'M
        (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2 x]
    by_cases hd : (ℓ : ℕ) ∣ M * q'
    · simp only [colsum, if_pos hd, if_neg h]
    · rw [colsum_of_not_dvd q' A M (M * q') ℓ hd]
      have hℓM : ¬ (ℓ : ℕ) ∣ M := fun h' => hd (h'.mul_right q')
      exact finrankAlong_heckeBetaC_eq_add_one q' A M ℓ h hq'M hℓM
        (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2 x.1 x.2

include hs hq5 hsq' hq'M in

theorem w_mul_edgeHecke_comm (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ (M * q') * s)
    (i j : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))) :
    (X.degeneracyData.w i : ℤ) * X.edgeHecke ℓ i j = (X.degeneracyData.w j : ℤ) * X.edgeHecke ℓ j i := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hq'Ms := not_q'_dvd_Ms M s q' hs hsq' hq'M
  have hℓq' : (ℓ : ℕ) ≠ q' := fun h => hℓ (dvd_of_eq_q' M s q' ℓ h)
  have hℓMs : ¬ (ℓ : ℕ) ∣ M * s := fun h' => hℓ (h'.trans ⟨q', by ring⟩)
  haveI := hasPrincipalDivisors_roof q' A (M * s) ℓ hℓq' hq'Ms
  have hwi : (X.degeneracyData.w i : ℤ) = ((Nat.toPNat' (placeWidth (M * s) i.1) : ℕ) : ℤ) := rfl
  have hwj : (X.degeneracyData.w j : ℤ) = ((Nat.toPNat' (placeWidth (M * s) j.1) : ℕ) : ℤ) := rfl
  rw [hwi, hwj]
  exact toPNat'_placeWidth_mul_comm q' hq5 A (M * s) ℓ hℓq' hq'Ms hℓMs (X.legsIntegral (M * s) ℓ).1
    (X.legsIntegral (M * s) ℓ).2 (X.edgeHecke ℓ) (edgeHecke_apply_and_vertexHecke_apply_of_ne X ℓ hℓq').1 i j

include hq5 hq'M in

theorem wV_mul_vertexHecke_comm (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ M * q')
    (i j : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))) :
    (Nat.toPNat' (placeWidth M i.1) : ℤ) * X.vertexHecke ℓ i j =
      (Nat.toPNat' (placeWidth M j.1) : ℤ) * X.vertexHecke ℓ j i := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hℓq' : (ℓ : ℕ) ≠ q' := fun h => hℓ (h ▸ dvd_mul_left q' M)
  have hℓM : ¬ (ℓ : ℕ) ∣ M := fun h' => hℓ (h'.mul_right q')
  haveI := hasPrincipalDivisors_roof q' A M ℓ hℓq' hq'M
  exact toPNat'_placeWidth_mul_comm q' hq5 A M ℓ hℓq' hq'M hℓM (X.legsIntegral M ℓ).1
    (X.legsIntegral M ℓ).2 (X.vertexHecke ℓ) (edgeHecke_apply_and_vertexHecke_apply_of_ne X ℓ hℓq').2 i j

include hs hsq' hq'M in
theorem exists_perm_edgeHecke :
    ∃ σ : Equiv.Perm ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), ∀ i j, X.edgeHecke ⟨q', Fact.out⟩ i j = if i = σ j then 1 else 0 :=
  exists_perm_of_frob q' A (M * s) (not_q'_dvd_Ms M s q' hs hsq' hq'M) X.frobData X.kronecker _
    (edgeHecke_apply_and_vertexHecke_apply_self X ⟨q', Fact.out⟩ rfl).1

include hq'M in
theorem exists_perm_vertexHecke :
    ∃ σ : Equiv.Perm ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)), ∀ i j, X.vertexHecke ⟨q', Fact.out⟩ i j = if i = σ j then 1 else 0 :=
  exists_perm_of_frob q' A M hq'M X.frobData X.kronecker _
    (edgeHecke_apply_and_vertexHecke_apply_self X ⟨q', Fact.out⟩ rfl).2

end Datum

end ModularCurve.SSLevelDatum.IdentEngines
p2m_reactivate "P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve.SSLevelDatum P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve.SSLevelDatum.IdentEngines"
p2m_reactivate "P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve.SSLevelDatum"
p2m_reactivate "P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws.ModularCurve"

open ModularCurve.SSLevelDatum.IdentEngines in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s) :
    ∃ (n₁ : Nat.Primes → ℤ) (_ : ∀ ℓ : Nat.Primes, HeckeRowSums (X.edgeHecke ℓ).transpose (n₁ ℓ))
      (n₂ : Nat.Primes → ℤ) (_ : ∀ ℓ : Nat.Primes, HeckeRowSums (X.vertexHecke ℓ).transpose (n₂ ℓ))
      (padj : Fin 2 → ((↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) →ₗ[ℤ]
        (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ)))
      (_ : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ),
        x ∈ characterLattice ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) →
        padj i x ∈ characterLattice ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))),
      (∀ ℓ ℓ' : Nat.Primes, Commute (X.edgeHecke ℓ) (X.edgeHecke ℓ')) ∧
      (∀ ℓ ℓ' : Nat.Primes, Commute (X.vertexHecke ℓ) (X.vertexHecke ℓ')) ∧
      (∀ (i : Fin 2) (ℓ : Nat.Primes), (ℓ : ℕ) ≠ s →
          CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) * X.edgeHecke ℓ =
            X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)) ∧
      (∀ x : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ,
          (∀ i : Fin 2,
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec x = 0) →
          ∀ i : Fin 2, (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec
            ((X.edgeHecke ⟨s, hs⟩).mulVec x) = 0) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * q') * s →
          ∀ i j, (X.degeneracyData.w i : ℤ) * X.edgeHecke ℓ i j = (X.degeneracyData.w j : ℤ) * X.edgeHecke ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' →
          ∀ i j, (Nat.toPNat' (placeWidth M i.1) : ℤ) * X.vertexHecke ℓ i j =
            (Nat.toPNat' (placeWidth M j.1) : ℤ) * X.vertexHecke ℓ j i) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ (M * q') * s → n₁ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M * q' → n₂ ℓ = ((ℓ : ℕ) : ℤ) + 1) ∧
      (∃ σ : Equiv.Perm ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
          ∀ i j, X.edgeHecke ⟨q', Fact.out⟩ i j = if i = σ j then 1 else 0) ∧
      (∃ σ : Equiv.Perm ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)),
          ∀ i j, X.vertexHecke ⟨q', Fact.out⟩ i j = if i = σ j then 1 else 0) ∧
      (∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ)
          (y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ),
          (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
              (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
            ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e) := by
  exact ⟨colsum q' A (M * s) ((M * q') * s), heckeRowSums_edgeHecke_transpose M s q' hs hq5 hsq' hq'M A X,
    colsum q' A M (M * q'), heckeRowSums_vertexHecke_transpose M s q' hq5 hq'M A X,
    padj M s q' A X, padj_mem_characterLattice M s q' hs hq5 hsq' hq'M hsM A X,
    commute_edgeHecke M s q' hs hsq' hq'M hsM A X,
    commute_vertexHecke M s q' hs hsq' hq'M hsM A X,
    degeneracyMatrix_mul_edgeHecke M s q' hs hsq' hq'M hsM A X,
    kernel_stable M s q' hs hsq' hq'M hsM A X,
    w_mul_edgeHecke_comm M s q' hs hq5 hsq' hq'M A X,
    wV_mul_vertexHecke_comm M s q' hq5 hq'M A X,
    colsum_of_not_dvd q' A (M * s) ((M * q') * s),
    colsum_of_not_dvd q' A M (M * q'),
    exists_perm_edgeHecke M s q' hs hsq' hq'M A X,
    exists_perm_vertexHecke M s q' hq'M A X,
    hadj M s q' hs hq5 hsq' hq'M A X⟩

end S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_exists_heckeRowSums_and_adjointPair_laws (solution)
