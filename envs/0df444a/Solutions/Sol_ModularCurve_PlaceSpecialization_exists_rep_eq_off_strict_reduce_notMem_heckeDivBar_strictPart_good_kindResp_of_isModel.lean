-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6a2ba5a4-bd38-5136-931e-06ae45183ff2

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_finset_isStrict_and_kind_of_mem_support_heckeDivBar_single_of_reduce_notMem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing
p2m_open "ModularCurve~mapDomain_mem_degZero_of_deg_eq~degree_mapDomain_of_deg_eq ModularCurve.PlaceSpecialization"

noncomputable section

namespace KindPrimeAux

theorem filter_zsmul {X : Type*} (p : X → Prop) [DecidablePred p] (n : ℤ) (f : X →₀ ℤ) :
    (n • f).filter p = n • f.filter p :=
  map_zsmul (Finsupp.filterAddHom p) n f

theorem heckeDivBar_eq_sum_smul {M : ℕ} [NeZero M] {ℓ : ℕ} [NeZero ℓ]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * ℓ))]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    {s : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M))} (hs : E.support ⊆ s) :
    heckeDivBar hα hβ E = ∑ V ∈ s, E V • heckeDivBar hα hβ (Finsupp.single V 1) := by
  conv_lhs => rw [← Finsupp.sum_single E,
    Finsupp.sum_of_support_subset E hs Finsupp.single fun i _ => Finsupp.single_zero i]
  rw [map_sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [← Finsupp.smul_single_one V (E V), map_zsmul]

section K5PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem not_isStrictFst_of_isStrictSnd
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hS : P.IsStrictSnd V) :
    ¬ P.IsStrictFst V := by
  intro hF
  have h1 : P.reduceFst V = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V) := hS.1
  rw [← hF.1] at h1
  exact hF.2 h1.symm

theorem support_fstDiv_subset (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.fstDiv D).support ⊆ D.support := by
  intro x hx
  simp only [ModularCurve.PlaceSpecialization.fstDiv, Finsupp.support_filter,
    Finset.mem_filter] at hx
  exact hx.1

theorem support_sndDiv_subset (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.sndDiv D).support ⊆ D.support := by
  intro x hx
  simp only [ModularCurve.PlaceSpecialization.sndDiv, Finsupp.support_filter,
    Finset.mem_filter] at hx
  exact hx.1

theorem isGoodDiv_heckeDivBar_and_fstDiv_sndDiv_comm_of_kindResp {ℓ : ℕ} [NeZero ℓ]
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))]
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hgood : P.IsGoodDiv E)
    (hE : ∀ V ∈ E.support, ∀ V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ))).support,
      (P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
        (P.IsStrictFst V → P.IsStrictFst V') ∧ (P.IsStrictSnd V → P.IsStrictSnd V')) :
    P.IsGoodDiv (heckeDivBar hαℓ hβℓ E) ∧
      P.fstDiv (heckeDivBar hαℓ hβℓ E) = heckeDivBar hαℓ hβℓ (P.fstDiv E) ∧
      P.sndDiv (heckeDivBar hαℓ hβℓ E) = heckeDivBar hαℓ hβℓ (P.sndDiv E) := by
  classical

  have hstrict : ∀ V' ∈ (heckeDivBar hαℓ hβℓ E).support, P.IsStrictFst V' ∨ P.IsStrictSnd V' := by
    intro V' hV'
    rw [heckeDivBar_eq_sum_smul hαℓ hβℓ _ subset_rfl] at hV'
    obtain ⟨V, hV, hV'V⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hV')
    exact (hE V hV V' (Finsupp.support_smul hV'V)).1
  have hexcl := not_isStrictFst_of_isStrictSnd P

  have hfiltF : ∀ V ∈ E.support, P.IsStrictFst V →
      (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).filter P.IsStrictFst
          = heckeDivBar hαℓ hβℓ (Finsupp.single V 1) ∧
        (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).filter P.IsStrictSnd = 0 := by
    intro V hV hF
    refine ⟨(Finsupp.filter_eq_self_iff _ _).mpr fun V' hV' => ?_,
      (Finsupp.filter_eq_zero_iff _ _).mpr fun V' hS' => ?_⟩
    · have hm : V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).support :=
        Finsupp.mem_support_iff.mpr hV'
      exact (hE V hV V' hm).2.1 hF
    · by_contra hne
      have hm : V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).support :=
        Finsupp.mem_support_iff.mpr hne
      exact hexcl V' hS' ((hE V hV V' hm).2.1 hF)
  have hfiltS : ∀ V ∈ E.support, P.IsStrictSnd V →
      (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).filter P.IsStrictFst = 0 ∧
        (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).filter P.IsStrictSnd
          = heckeDivBar hαℓ hβℓ (Finsupp.single V 1) := by
    intro V hV hS
    refine ⟨(Finsupp.filter_eq_zero_iff _ _).mpr fun V' hF' => ?_,
      (Finsupp.filter_eq_self_iff _ _).mpr fun V' hV' => ?_⟩
    · by_contra hne
      have hm : V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).support :=
        Finsupp.mem_support_iff.mpr hne
      exact hexcl V' ((hE V hV V' hm).2.2 hS) hF'
    · have hm : V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V 1)).support :=
        Finsupp.mem_support_iff.mpr hV'
      exact (hE V hV V' hm).2.2 hS
  have hfst : P.fstDiv (heckeDivBar hαℓ hβℓ E) = heckeDivBar hαℓ hβℓ (P.fstDiv E) := by
    rw [heckeDivBar_eq_sum_smul hαℓ hβℓ (P.fstDiv E) (support_fstDiv_subset P E),
      heckeDivBar_eq_sum_smul hαℓ hβℓ _ subset_rfl]
    simp only [ModularCurve.PlaceSpecialization.fstDiv, Finsupp.filter_sum, filter_zsmul,
      Finsupp.filter_apply]
    refine Finset.sum_congr rfl fun V hV => ?_
    rcases hgood V hV with hF | hS
    · rw [if_pos hF, (hfiltF V hV hF).1]
    · rw [if_neg (hexcl V hS), (hfiltS V hV hS).1, smul_zero, zero_smul]
  have hsnd : P.sndDiv (heckeDivBar hαℓ hβℓ E) = heckeDivBar hαℓ hβℓ (P.sndDiv E) := by
    rw [heckeDivBar_eq_sum_smul hαℓ hβℓ (P.sndDiv E) (support_sndDiv_subset P E),
      heckeDivBar_eq_sum_smul hαℓ hβℓ _ subset_rfl]
    simp only [ModularCurve.PlaceSpecialization.sndDiv, Finsupp.filter_sum, filter_zsmul,
      Finsupp.filter_apply]
    refine Finset.sum_congr rfl fun V hV => ?_
    rcases hgood V hV with hF | hS
    · rw [if_neg (fun hS => hexcl V hS hF), (hfiltF V hV hF).2, smul_zero, zero_smul]
    · rw [if_pos hS, (hfiltS V hV hS).2]
  exact ⟨fun V' hV' => hstrict V' hV', hfst, hsnd⟩

theorem isGoodDiv_heckeDivBar_and_fstDiv_sndDiv_comm_of_forall_reduce_notMem {ℓ : ℕ} [NeZero ℓ]
    (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
    (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))]
    (T : Finset (Place k ↥(modularFunctionFieldC k N)))
    (hT : ∀ V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst V ∉ T → P.reduceSnd V ∉ T →
      V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ))).support →
        (P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
        (P.IsStrictFst V → P.IsStrictFst V') ∧
        (P.IsStrictSnd V → P.IsStrictSnd V'))
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hgood : P.IsGoodDiv E)
    (hoff : ∀ V ∈ E.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) :
    P.IsGoodDiv (heckeDivBar hαℓ hβℓ E) ∧
      P.fstDiv (heckeDivBar hαℓ hβℓ E) = heckeDivBar hαℓ hβℓ (P.fstDiv E) ∧
      P.sndDiv (heckeDivBar hαℓ hβℓ E) = heckeDivBar hαℓ hβℓ (P.sndDiv E) :=
  isGoodDiv_heckeDivBar_and_fstDiv_sndDiv_comm_of_kindResp P hαℓ hβℓ E hgood
    fun V hV V' hV' => hT V V' (hoff V hV).1 (hoff V hV).2 hV'

end K5PlaceSpecialization

theorem degree_mapDomain_of_deg_eq {K₁ F₁ K₂ F₂ : Type*}
    [Field K₁] [Field F₁] [Algebra K₁ F₁] [Field K₂] [Field F₂] [Algebra K₂ F₂]
    (r : Place K₁ F₁ → Place K₂ F₂) (hdeg : ∀ w, (r w).deg = w.deg) (D : Divisor K₁ F₁) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add w n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, hdeg]

theorem mapDomain_mem_degZero_of_deg_eq {K₁ F₁ K₂ F₂ : Type*}
    [Field K₁] [Field F₁] [Algebra K₁ F₁] [Field K₂] [Field F₂] [Algebra K₂ F₂]
    (r : Place K₁ F₁ → Place K₂ F₂) (hdeg : ∀ w, (r w).deg = w.deg) {D : Divisor K₁ F₁} :
    Finsupp.mapDomain r D ∈ Divisor.degZero (K := K₂) (F := F₂)
      ↔ D ∈ Divisor.degZero (K := K₁) (F := F₁) := by
  rw [Divisor.mem_degZero, Divisor.mem_degZero, degree_mapDomain_of_deg_eq r hdeg]

section K2PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem deg_reduceFst [IsAlgClosed k] (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.reduceFst V).deg = V.deg := by
  rw [place_deg_eq_one_of_isAlgClosed k N (P.reduceFst V), deg_eq_one_modularFunctionFieldBar (N * q) V]

theorem deg_reduceSnd [IsAlgClosed k] (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    (P.reduceSnd V).deg = V.deg := by
  rw [place_deg_eq_one_of_isAlgClosed k N (P.reduceSnd V), deg_eq_one_modularFunctionFieldBar (N * q) V]

theorem mapDomain_reduceFst_fstDiv_apply_eq_zero
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv E) w = 0 := by
  classical
  by_contra hne
  obtain ⟨V', hV', hVw⟩ :=
    Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne))
  have hF : P.IsStrictFst V' := by
    by_contra hnot
    exact Finsupp.mem_support_iff.mp hV'
      (by simp [ModularCurve.PlaceSpecialization.fstDiv, hnot])
  exact hF.2 (by rw [hVw]; exact hw)

theorem mapDomain_reduceSnd_sndDiv_apply_eq_zero
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w) :
    Finsupp.mapDomain P.reduceSnd (P.sndDiv E) w = 0 := by
  classical
  by_contra hne
  obtain ⟨V', hV', hVw⟩ :=
    Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne))
  have hS : P.IsStrictSnd V' := by
    by_contra hnot
    exact Finsupp.mem_support_iff.mp hV'
      (by simp [ModularCurve.PlaceSpecialization.sndDiv, hnot])
  exact hS.2 (by rw [hVw]; exact hw)

theorem glueData_mem_admissible_of_fstDiv_sndDiv_mem_degZero [DecidableEq k] [IsAlgClosed k]
    (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hF0 : P.fstDiv E ∈ Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar (N * q)))
    (hS0 : P.sndDiv E ∈ Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar (N * q))) :
    P.glueData (nodePairsOfPlaces (arithFrobC q k N) W) E
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) := by

  have hfixW : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr
      (frobOnPlacesGeomLevel k N data hKr w) = w := fun w hw =>
    frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
      k N hqN data hKr w ((hW w).mp hw)
  have hfixW' : ∀ w ∈ W, frobOnPlacesGeomLevel k N data hKr
      (frobOnPlacesGeomLevel k N data hKr (arithFrobC q k N • w)) = arithFrobC q k N • w :=
    fun w hw =>
      frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
        k N hqN data hKr _ (arithFrobC_smul_mem_ssPlaces q N k w ((hW w).mp hw))
  refine (GluingData.mem_admissible _).mpr ⟨?_, ?_, fun s hs => ⟨?_, ?_⟩⟩
  · show Finsupp.mapDomain P.reduceFst (P.fstDiv E) ∈ _
    exact (mapDomain_mem_degZero_of_deg_eq P.reduceFst (deg_reduceFst P)).mpr hF0
  · show Finsupp.mapDomain P.reduceSnd (P.sndDiv E) ∈ _
    exact (mapDomain_mem_degZero_of_deg_eq P.reduceSnd (deg_reduceSnd P)).mpr hS0
  · exact mapDomain_reduceFst_fstDiv_apply_eq_zero P E s.1
      (hfixW s.1 (fst_mem_of_mem_nodePairsOfPlaces hs))
  · show Finsupp.mapDomain P.reduceSnd (P.sndDiv E) s.2 = 0
    rw [snd_eq_of_mem_nodePairsOfPlaces hs]
    exact mapDomain_reduceSnd_sndDiv_apply_eq_zero P E _
      (hfixW' s.1 (fst_mem_of_mem_nodePairsOfPlaces hs))

theorem isGoodClass_mk_of_isGoodDiv_of_fstDiv_sndDiv_mem_degZero [DecidableEq k] [IsAlgClosed k]
    (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
    (hF0 : P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N * q)))
    (hS0 : P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N * q))) :
    P.IsGoodClass (nodePairsOfPlaces (arithFrobC q k N) W) (Pic0.mk D) :=
  ⟨D, hgood, glueData_mem_admissible_of_fstDiv_sndDiv_mem_degZero P hqN W hW _ hF0 hS0, rfl⟩

end K2PlaceSpecialization

section Generic

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem fstDiv_apply_of {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : P.IsStrictFst V) : P.fstDiv D V = D V := by
  classical
  simp [ModularCurve.PlaceSpecialization.fstDiv, h]

theorem fstDiv_apply_of_not {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : ¬ P.IsStrictFst V) : P.fstDiv D V = 0 := by
  classical
  simp [ModularCurve.PlaceSpecialization.fstDiv, h]

theorem sndDiv_apply_of {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : P.IsStrictSnd V) : P.sndDiv D V = D V := by
  classical
  simp [ModularCurve.PlaceSpecialization.sndDiv, h]

theorem sndDiv_apply_of_not {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : ¬ P.IsStrictSnd V) : P.sndDiv D V = 0 := by
  classical
  simp [ModularCurve.PlaceSpecialization.sndDiv, h]

theorem fstDiv_add (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.fstDiv (D + E) = P.fstDiv D + P.fstDiv E := by
  classical
  unfold fstDiv; convert Finsupp.filter_add

theorem sndDiv_add (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.sndDiv (D + E) = P.sndDiv D + P.sndDiv E := by
  classical
  unfold sndDiv; convert Finsupp.filter_add

def fstDivHom : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) →+ Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) where
  toFun := P.fstDiv
  map_zero' := P.fstDiv_zero
  map_add' := fstDiv_add P

def sndDivHom : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) →+ Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) where
  toFun := P.sndDiv
  map_zero' := P.sndDiv_zero
  map_add' := sndDiv_add P

theorem fstDivHom_apply (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : fstDivHom P D = P.fstDiv D := rfl

theorem sndDivHom_apply (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : sndDivHom P D = P.sndDiv D := rfl

theorem fstDiv_sub (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.fstDiv (D - E) = P.fstDiv D - P.fstDiv E := by
  rw [← fstDivHom_apply, map_sub, fstDivHom_apply, fstDivHom_apply]

theorem sndDiv_sub (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.sndDiv (D - E) = P.sndDiv D - P.sndDiv E := by
  rw [← sndDivHom_apply, map_sub, sndDivHom_apply, sndDivHom_apply]

theorem fstDiv_zsmul (n : ℤ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.fstDiv (n • D) = n • P.fstDiv D := by
  rw [← fstDivHom_apply, map_zsmul, fstDivHom_apply]

theorem sndDiv_zsmul (n : ℤ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.sndDiv (n • D) = n • P.sndDiv D := by
  rw [← sndDivHom_apply, map_zsmul, sndDivHom_apply]

theorem fstDiv_single_of_isStrictFst {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : P.IsStrictFst V) (n : ℤ) :
    P.fstDiv (Finsupp.single V n) = Finsupp.single V n := by
  ext U
  by_cases hU : U = V
  · subst hU; exact fstDiv_apply_of P hV
  · by_cases h : P.IsStrictFst U
    · exact fstDiv_apply_of P h
    · rw [fstDiv_apply_of_not P h, Finsupp.single_eq_of_ne hU]

theorem fstDiv_single_of_not {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : ¬ P.IsStrictFst V) (n : ℤ) :
    P.fstDiv (Finsupp.single V n) = 0 := by
  ext U
  rw [Finsupp.zero_apply]
  by_cases hU : U = V
  · subst hU; exact fstDiv_apply_of_not P hV
  · by_cases h : P.IsStrictFst U
    · rw [fstDiv_apply_of P h, Finsupp.single_eq_of_ne hU]
    · exact fstDiv_apply_of_not P h

theorem sndDiv_single_of_isStrictSnd {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : P.IsStrictSnd V) (n : ℤ) :
    P.sndDiv (Finsupp.single V n) = Finsupp.single V n := by
  ext U
  by_cases hU : U = V
  · subst hU; exact sndDiv_apply_of P hV
  · by_cases h : P.IsStrictSnd U
    · exact sndDiv_apply_of P h
    · rw [sndDiv_apply_of_not P h, Finsupp.single_eq_of_ne hU]

theorem sndDiv_single_of_not {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : ¬ P.IsStrictSnd V) (n : ℤ) :
    P.sndDiv (Finsupp.single V n) = 0 := by
  ext U
  rw [Finsupp.zero_apply]
  by_cases hU : U = V
  · subst hU; exact sndDiv_apply_of_not P hV
  · by_cases h : P.IsStrictSnd U
    · rw [sndDiv_apply_of P h, Finsupp.single_eq_of_ne hU]
    · exact sndDiv_apply_of_not P h

theorem fstDiv_fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.fstDiv (P.fstDiv D) = P.fstDiv D := by
  ext V
  by_cases h : P.IsStrictFst V
  · rw [fstDiv_apply_of P h]
  · rw [fstDiv_apply_of_not P h, fstDiv_apply_of_not P h]

theorem sndDiv_sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.sndDiv (P.sndDiv D) = P.sndDiv D := by
  ext V
  by_cases h : P.IsStrictSnd V
  · rw [sndDiv_apply_of P h]
  · rw [sndDiv_apply_of_not P h, sndDiv_apply_of_not P h]

theorem fstDiv_sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.fstDiv (P.sndDiv D) = 0 := by
  ext V
  rw [Finsupp.zero_apply]
  by_cases hF : P.IsStrictFst V
  · rw [fstDiv_apply_of P hF, sndDiv_apply_of_not P (fun hS => not_isStrictFst_of_isStrictSnd P V hS hF)]
  · rw [fstDiv_apply_of_not P hF]

theorem sndDiv_fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.sndDiv (P.fstDiv D) = 0 := by
  ext V
  rw [Finsupp.zero_apply]
  by_cases hS : P.IsStrictSnd V
  · rw [sndDiv_apply_of P hS, fstDiv_apply_of_not P (not_isStrictFst_of_isStrictSnd P V hS)]
  · rw [sndDiv_apply_of_not P hS]

theorem fstDiv_add_sndDiv_apply_of_strict (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hV : P.IsStrictFst V ∨ P.IsStrictSnd V) : (P.fstDiv D + P.sndDiv D) V = D V := by
  rw [Finsupp.add_apply]
  rcases hV with hF | hS
  · rw [fstDiv_apply_of P hF, sndDiv_apply_of_not P (fun hS => not_isStrictFst_of_isStrictSnd P V hS hF), add_zero]
  · rw [fstDiv_apply_of_not P (not_isStrictFst_of_isStrictSnd P V hS), sndDiv_apply_of P hS, zero_add]

theorem fstDiv_add_sndDiv_apply_of_not (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hV : ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V)) : (P.fstDiv D + P.sndDiv D) V = 0 := by
  rw [Finsupp.add_apply, fstDiv_apply_of_not P (fun h => hV (Or.inl h)),
    sndDiv_apply_of_not P (fun h => hV (Or.inr h)), add_zero]

theorem isGoodDiv_fstDiv_add_sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : P.IsGoodDiv (P.fstDiv D + P.sndDiv D) := by
  intro V hV
  by_contra h
  exact (Finsupp.mem_support_iff.mp hV) (fstDiv_add_sndDiv_apply_of_not P D h)

theorem fstDiv_add_sndDiv_eq_self_of_isGoodDiv {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hD : P.IsGoodDiv D) :
    P.fstDiv D + P.sndDiv D = D := by
  ext V
  by_cases hV : P.IsStrictFst V ∨ P.IsStrictSnd V
  · exact fstDiv_add_sndDiv_apply_of_strict P D hV
  · rw [fstDiv_add_sndDiv_apply_of_not P D hV]
    by_contra hne
    exact hV (hD V (Finsupp.mem_support_iff.mpr (Ne.symm hne)))

end Generic

end KindPrimeAux

end

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 6400000 in
open KindPrimeAux in

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
          ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))],
          ∀ (T₀ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
            (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
              (F := ↥(modularFunctionFieldBar (N * q))))),
              ∃ D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q)))),

                Pic0.mk D₁ = Pic0.mk D ∧

                (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
                  ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) →
                    (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V = (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V) ∧

                (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  (P.IsStrictFst V ∨ P.IsStrictSnd V) → P.reduceFst V ∉ T₀ ∧ P.reduceSnd V ∉ T₀) ∧

                P.IsGoodDiv (heckeDivBar hαℓ hβℓ
                  (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) ∧
                P.fstDiv (heckeDivBar hαℓ hβℓ
                    (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
                  = heckeDivBar hαℓ hβℓ (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
                P.sndDiv (heckeDivBar hαℓ hβℓ
                    (P.fstDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
                  = heckeDivBar hαℓ hβℓ (P.sndDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))) := by
  intro W hW data hKr hα hβ P R hR hRL hNV hO ℓ hℓq
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  intro hαℓ hβℓ _ T₀ D
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  set φ := frobOnPlacesGeomLevel (ResidueField A) N data hKr with hφ
  have hφinj : Function.Injective φ := frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr
  set Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) := (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) with hDv

  obtain ⟨Texc, hTexc⟩ :=
    ModularCurve.PlaceSpecialization.exists_finset_isStrict_and_kind_of_mem_support_heckeDivBar_single_of_reduce_notMem
      N q hq hqN A hA data hKr hα hβ P ℓ hℓq hαℓ hβℓ
  set Tstar : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) := T₀ ∪ Texc
    with hTstar

  set B : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) :=
    Tstar ∪ Tstar.preimage φ (hφinj.injOn) with hB
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, -, -, hQ₁B, hQ₂B⟩ :=
    ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem P hqN B 1 1
  set V₁ := Q₁ 0 with hV₁
  set V₂ := Q₂ 0 with hV₂
  have hV₁F : P.IsStrictFst V₁ := hQ₁ 0
  have hV₂S : P.IsStrictSnd V₂ := hQ₂ 0
  have hmemB : ∀ w, w ∉ B → w ∉ Tstar ∧ φ w ∉ Tstar := fun w hw =>
    ⟨fun h => hw (Finset.mem_union_left _ h),
      fun h => hw (Finset.mem_union_right _ (Finset.mem_preimage.mpr h))⟩
  have hV₁T : P.reduceFst V₁ ∉ Tstar ∧ P.reduceSnd V₁ ∉ Tstar := by
    obtain ⟨h1, h2⟩ := hmemB _ (hQ₁B 0)
    exact ⟨h1, by rw [← hV₁F.1]; exact h2⟩
  have hV₂T : P.reduceFst V₂ ∉ Tstar ∧ P.reduceSnd V₂ ∉ Tstar := by
    obtain ⟨h1, h2⟩ := hmemB _ (hQ₂B 0)
    exact ⟨by rw [hV₂S.1]; exact h2, h1⟩
  have hV₂F : ¬ P.IsStrictFst V₂ := not_isStrictFst_of_isStrictSnd P V₂ hV₂S
  have hV₁S : ¬ P.IsStrictSnd V₁ := fun h => not_isStrictFst_of_isStrictSnd P V₁ h hV₁F

  have hdeg1 : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), (V.deg : ℤ) = 1 := fun V => by
    rw [deg_eq_one_modularFunctionFieldBar (N * q) V]; rfl

  set S : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) := P.fstDiv Dv + P.sndDiv Dv with hS
  set a : ℤ := Divisor.degree (P.fstDiv Dv) with ha
  set b : ℤ := Divisor.degree (P.sndDiv Dv) with hb
  set S₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) := S - a • Finsupp.single V₁ 1 - b • Finsupp.single V₂ 1 with hS₀
  have hfstS : P.fstDiv S = P.fstDiv Dv := by
    rw [hS, fstDiv_add, fstDiv_fstDiv, fstDiv_sndDiv, add_zero]
  have hsndS : P.sndDiv S = P.sndDiv Dv := by
    rw [hS, sndDiv_add, sndDiv_fstDiv, sndDiv_sndDiv, zero_add]
  have hfstS₀ : P.fstDiv S₀ = P.fstDiv Dv - a • Finsupp.single V₁ 1 := by
    rw [hS₀, fstDiv_sub, fstDiv_sub, hfstS, fstDiv_zsmul, fstDiv_zsmul,
      fstDiv_single_of_isStrictFst P hV₁F, fstDiv_single_of_not P hV₂F, smul_zero, sub_zero]
  have hsndS₀ : P.sndDiv S₀ = P.sndDiv Dv - b • Finsupp.single V₂ 1 := by
    rw [hS₀, sndDiv_sub, sndDiv_sub, hsndS, sndDiv_zsmul, sndDiv_zsmul,
      sndDiv_single_of_not P hV₁S, sndDiv_single_of_isStrictSnd P hV₂S, smul_zero, sub_zero]
  have hdegF₀ : Divisor.degree (P.fstDiv S₀) = 0 := by
    rw [hfstS₀, map_sub, map_zsmul, Divisor.degree_single, hdeg1, ← ha]; ring
  have hdegS₀ : Divisor.degree (P.sndDiv S₀) = 0 := by
    rw [hsndS₀, map_sub, map_zsmul, Divisor.degree_single, hdeg1, ← hb]; ring
  have hS₀good : P.IsGoodDiv S₀ := by
    intro V hV
    by_contra h
    apply Finsupp.mem_support_iff.mp hV
    rw [hS₀, Finsupp.sub_apply, Finsupp.sub_apply, hS, fstDiv_add_sndDiv_apply_of_not P Dv h,
      Finsupp.smul_apply, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne (fun hV1 => h (Or.inl (by rw [hV1]; exact hV₁F))),
      Finsupp.single_eq_of_ne (fun hV2 => h (Or.inr (by rw [hV2]; exact hV₂S))), smul_zero, smul_zero, sub_zero, sub_zero]
  have hS₀deg : S₀ ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, ← fstDiv_add_sndDiv_eq_self_of_isGoodDiv P hS₀good, map_add, hdegF₀,
      hdegS₀, add_zero]
  have hadm₀ := glueData_mem_admissible_of_fstDiv_sndDiv_mem_degZero P hqN W hW S₀
    (Divisor.mem_degZero.mpr hdegF₀) (Divisor.mem_degZero.mpr hdegS₀)
  have hx : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (Pic0.mk ⟨S₀, hS₀deg⟩) :=
    ⟨⟨S₀, hS₀deg⟩, hS₀good, hadm₀, rfl⟩

  obtain ⟨D', hD'good, -, hmk', hD'T⟩ :=
    PlaceSpecialization.ProlongationTuple.exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
      N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hNV hO Tstar _ hx

  set S₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) := (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) + a • Finsupp.single V₁ 1 + b • Finsupp.single V₂ 1 with hS₁
  have hS₁good : P.IsGoodDiv S₁ := by
    intro V hV
    rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
    · rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
      · exact hD'good V h'
      · exact Or.inl ((Finset.mem_singleton.mp (Finsupp.support_single_subset (Finsupp.support_smul h'))) ▸ hV₁F)
    · exact Or.inr ((Finset.mem_singleton.mp (Finsupp.support_single_subset (Finsupp.support_smul h))) ▸ hV₂S)
  have hS₁T : ∀ V ∈ S₁.support, P.reduceFst V ∉ Tstar ∧ P.reduceSnd V ∉ Tstar := by
    intro V hV
    rcases Finset.mem_union.mp (Finsupp.support_add hV) with h | h
    · rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
      · exact hD'T V h'
      · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset (Finsupp.support_smul h'))]; exact hV₁T
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset (Finsupp.support_smul h))]; exact hV₂T
  have hdegS₁ : Divisor.degree S₁ = Divisor.degree S := by
    have hD'0 : Divisor.degree (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = 0 := D'.2
    have hSab : Divisor.degree S = a + b := by rw [hS, map_add]
    rw [hS₁, map_add, map_add, map_zsmul, map_zsmul, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1,
      hD'0, hSab]; ring
  have hD₁deg : S₁ + (Dv - S) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
    rw [Divisor.mem_degZero, map_add, map_sub, hdegS₁, add_sub_cancel]
    exact D.2

  have hD₁strict : ∀ V, (P.IsStrictFst V ∨ P.IsStrictSnd V) → (S₁ + (Dv - S)) V = S₁ V := fun V hV => by
    rw [Finsupp.add_apply, Finsupp.sub_apply, hS, fstDiv_add_sndDiv_apply_of_strict P Dv hV, sub_self, add_zero]
  have hS₁zero : ∀ V, ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) → S₁ V = 0 := fun V hV => by
    by_contra hne
    exact hV (hS₁good V (Finsupp.mem_support_iff.mpr hne))
  have hD₁off : ∀ V, ¬ (P.IsStrictFst V ∨ P.IsStrictSnd V) → (S₁ + (Dv - S)) V = Dv V := fun V hV => by
    rw [Finsupp.add_apply, Finsupp.sub_apply, hS₁zero V hV, hS, fstDiv_add_sndDiv_apply_of_not P Dv hV,
      sub_zero, zero_add]
  have hstrictPart : P.fstDiv (S₁ + (Dv - S)) + P.sndDiv (S₁ + (Dv - S)) = S₁ := by
    ext V
    by_cases hV : P.IsStrictFst V ∨ P.IsStrictSnd V
    · rw [fstDiv_add_sndDiv_apply_of_strict P _ hV, hD₁strict V hV]
    · rw [fstDiv_add_sndDiv_apply_of_not P _ hV, hS₁zero V hV]
  have hfstD₁ : P.fstDiv (S₁ + (Dv - S)) = P.fstDiv S₁ := by
    have h := congrArg P.fstDiv hstrictPart
    rwa [fstDiv_add, fstDiv_fstDiv, fstDiv_sndDiv, add_zero] at h
  have hsndD₁ : P.sndDiv (S₁ + (Dv - S)) = P.sndDiv S₁ := by
    have h := congrArg P.sndDiv hstrictPart
    rwa [sndDiv_add, sndDiv_fstDiv, sndDiv_sndDiv, zero_add] at h

  have hTexc' : ∀ V V' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), P.reduceFst V ∉ Texc → P.reduceSnd V ∉ Texc →
      V' ∈ (heckeDivBar hαℓ hβℓ (Finsupp.single V (1 : ℤ))).support →
        (P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧ (P.IsStrictFst V → P.IsStrictFst V') ∧
          (P.IsStrictSnd V → P.IsStrictSnd V') := fun V V' h1 h2 h3 => hTexc V V' h1 h2 h3
  have hS₁Texc : ∀ V ∈ S₁.support, P.reduceFst V ∉ Texc ∧ P.reduceSnd V ∉ Texc := fun V hV =>
    ⟨fun h => (hS₁T V hV).1 (Finset.mem_union_right _ h), fun h => (hS₁T V hV).2 (Finset.mem_union_right _ h)⟩
  obtain ⟨hKgood, hKfst, hKsnd⟩ :=
    isGoodDiv_heckeDivBar_and_fstDiv_sndDiv_comm_of_forall_reduce_notMem P hαℓ hβℓ Texc hTexc' S₁ hS₁good hS₁Texc

  refine ⟨⟨S₁ + (Dv - S), hD₁deg⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply QuotientAddGroup.eq.mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    have hq' := QuotientAddGroup.eq.mp hmk'
    rw [AddSubgroup.mem_addSubgroupOf] at hq'
    have : ((-(⟨S₁ + (Dv - S), hD₁deg⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))))) + D :
          ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
        = ((-D' + ⟨S₀, hS₀deg⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q))))) : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
      push_cast
      rw [hS₁, hS₀, ← hDv]
      abel
    rw [this]
    exact hq'
  ·
    intro V hV
    exact hD₁off V hV
  ·
    intro V hV hVs
    have hV' : V ∈ S₁.support := by
      rw [Finsupp.mem_support_iff] at hV ⊢
      rwa [hD₁strict V hVs] at hV
    exact ⟨fun h => (hS₁T V hV').1 (Finset.mem_union_left _ h), fun h => (hS₁T V hV').2 (Finset.mem_union_left _ h)⟩
  ·
    show P.IsGoodDiv (heckeDivBar hαℓ hβℓ (P.fstDiv (S₁ + (Dv - S)) + P.sndDiv (S₁ + (Dv - S))))
    rw [hstrictPart]; exact hKgood
  · show P.fstDiv (heckeDivBar hαℓ hβℓ (P.fstDiv (S₁ + (Dv - S)) + P.sndDiv (S₁ + (Dv - S))))
      = heckeDivBar hαℓ hβℓ (P.fstDiv (S₁ + (Dv - S)))
    rw [hstrictPart, hfstD₁]; exact hKfst
  · show P.sndDiv (heckeDivBar hαℓ hβℓ (P.fstDiv (S₁ + (Dv - S)) + P.sndDiv (S₁ + (Dv - S))))
      = heckeDivBar hαℓ hβℓ (P.sndDiv (S₁ + (Dv - S)))
    rw [hstrictPart, hsndD₁]; exact hKsnd

end S_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_rep_eq_off_strict_reduce_notMem_heckeDivBar_strictPart_good_kindResp_of_isModel (solution)
