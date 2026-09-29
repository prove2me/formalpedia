-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/45e84811-4f01-5eab-9ffb-22f3ae98243c

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_or_isStrictSnd_iff
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "nodePairsOfPlaces mem_nodePairsOfPlaces_iff ssPlaces ModularPolynomialData modularFunctionFieldC frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence arithFrobC instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldBar JZero PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral hasPrincipalDivisors_modularFunctionFieldBar_unconditional frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed arithFrobC_smul_mem_ssPlaces_univ"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv glueData IsGoodClass glueData_zero mk ProlongationTuple ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem ProlongationTuple.glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd isStrictFst_or_isStrictSnd_iff"
namespace Recut
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

theorem fstDiv_add (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.fstDiv (D + E) = P.fstDiv D + P.fstDiv E := by
  classical
  unfold fstDiv; convert Finsupp.filter_add

theorem sndDiv_add (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.sndDiv (D + E) = P.sndDiv D + P.sndDiv E := by
  classical
  unfold sndDiv; convert Finsupp.filter_add

theorem glueData_add (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.glueData S (D + E) = P.glueData S D + P.glueData S E := by
  unfold glueData
  rw [fstDiv_add, sndDiv_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add]
  ext <;> simp

def glueDataHom (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) →+ GluingData k (modularFunctionFieldC k N) S where
  toFun := P.glueData S
  map_zero' := P.glueData_zero S
  map_add' := glueData_add P S

theorem glueDataHom_apply (S : Finset (Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : glueDataHom P S D = P.glueData S D := rfl

theorem reduceSnd_not_fixed_of_strict (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (h : P.IsStrictFst W ∨ P.IsStrictSnd W) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W)) ≠ P.reduceSnd W := by
  rcases h with ⟨h1, h2⟩ | ⟨-, h2⟩
  · intro hfix
    apply h2
    apply frobOnPlacesGeomLevel_injective k N data hKr
    rw [h1]
    exact hfix
  · exact h2

end ModularCurve.PlaceSpecialization.Recut

end

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option maxHeartbeats 6400000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel.ModularCurve.PlaceSpecialization in
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : P.ProlongationTuple) (hR : R.IsModel) (hNR : R.RegularityLaw W)
      (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
          (x : JZero (N * q)),
            P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) x →
              ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q)))),
                P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
                P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
                  ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
                Pic0.mk D = x ∧
                ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by
  intro W hW data hKr hα hβ P R hR hNR hval hO T x hx
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  have ssfix : ∀ w, w ∈ ssPlaces q N (ResidueField A) →
      frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr w) = w :=
    fun w hw => ModularCurve.frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
      (ResidueField A) N hqN data hKr w hw

  let φ := frobOnPlacesGeomLevel (ResidueField A) N data hKr
  let S := nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W
  let T' : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) := T \ W

  have hWfix : ∀ s ∈ S, φ (φ s.1) = s.1 ∧ φ (φ s.2) = s.2 := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff _ W s).mp hs
    have hss := (hW w).mp hw
    refine ⟨ssfix w hss, ?_⟩
    exact ssfix _ (arithFrobC_smul_mem_ssPlaces_univ q N (ResidueField A) w hss)

  have MOV := ProlongationTuple.exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem
    N q hq hqN A hA W hW data hKr hα hβ P R hR hNR hval hO T'
    (fun t ht hss => (Finset.mem_sdiff.mp ht).2 ((hW t).mpr hss))

  have HPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)

  let bad : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) →
      Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    fun D => D.support.filter fun V => P.reduceFst V ∈ T' ∨ P.reduceSnd V ∈ T'
  have mem_bad : ∀ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V,
      V ∈ bad D ↔ V ∈ D.support ∧ (P.reduceFst V ∈ T' ∨ P.reduceSnd V ∈ T') := fun D V => Finset.mem_filter

  suffices key : ∀ n : ℕ, ∀ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
      P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
      P.glueData S D ∈ GluingData.admissible S →
      (bad D).card ≤ n →
      ∃ D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
        P.IsGoodDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
        P.glueData S D' ∈ GluingData.admissible S ∧ Pic0.mk D' = Pic0.mk D ∧ bad D' = ∅ by
    obtain ⟨D₀, hgood₀, hadm₀, hmk₀⟩ := hx
    obtain ⟨D', hg', ha', hmk', hbad'⟩ := key _ D₀ hgood₀ hadm₀ le_rfl
    refine ⟨D', hg', ha', hmk'.trans hmk₀, ?_⟩
    intro V hV
    have hstr := hg' V hV
    have h1 : φ (φ (P.reduceFst V)) ≠ P.reduceFst V := (P.isStrictFst_or_isStrictSnd_iff V).mp hstr
    have h2 : φ (φ (P.reduceSnd V)) ≠ P.reduceSnd V := Recut.reduceSnd_not_fixed_of_strict P V hstr
    have hnotW : ∀ w, φ (φ w) ≠ w → w ∉ W := fun w hw hmem =>
      hw (ssfix w ((hW w).mp hmem))
    have hnotbad : ¬ (P.reduceFst V ∈ T' ∨ P.reduceSnd V ∈ T') := by
      intro h
      have : V ∈ bad D' := (mem_bad _ V).mpr ⟨hV, h⟩
      rw [hbad'] at this
      exact absurd this (Finset.notMem_empty V)
    constructor
    · intro hT
      rcases Finset.mem_sdiff.not.mp (fun h => hnotbad (Or.inl h)) with h
      exact h ⟨hT, hnotW _ h1⟩
    · intro hT
      exact (fun h => hnotbad (Or.inr h)) (Finset.mem_sdiff.mpr ⟨hT, hnotW _ h2⟩)
  intro n
  induction n with
  | zero =>
    intro D hg ha hcard
    exact ⟨D, hg, ha, rfl, Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)⟩
  | succ n ih =>
    intro D hg ha hcard
    by_cases hempty : bad D = ∅
    · exact ⟨D, hg, ha, rfl, hempty⟩
    obtain ⟨V, hVbad⟩ := Finset.nonempty_of_ne_empty hempty
    obtain ⟨hVsupp, hVT⟩ := (mem_bad _ V).mp hVbad

    obtain ⟨f, Df, hf0, ⟨h₁, h₂, hr₁, hr₂⟩, hDf, hDfV, hstrict, havoid⟩ := MOV V hVT

    have hDf0 : Df ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) := by
      obtain ⟨D'', hD'', hdeg⟩ := HPD.exists_divisor f hf0
      have : Df = D'' := Finsupp.ext fun v => (hDf v).trans (hD'' v).symm
      rw [Divisor.mem_degZero, this, hdeg]

    have hVstrict : P.IsStrictFst V ∨ P.IsStrictSnd V := hg V hVsupp
    have hDfgood : P.IsGoodDiv Df := by
      intro U hU
      by_cases hUV : U = V
      · rw [hUV]; exact hVstrict
      · exact hstrict U hU hUV

    set c : ℤ := (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V with hc
    let D₁ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))) :=
      ⟨(D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - c • Df,
        sub_mem D.2 (AddSubgroup.zsmul_mem _ hDf0 c)⟩
    have hD₁coe : (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) =
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) - c • Df := rfl

    have hsupp : ∀ U ∈ (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        U ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support ∨ U ∈ Df.support := by
      intro U hU
      by_contra hnot
      simp only [not_or, Finsupp.mem_support_iff, not_not] at hnot
      rw [Finsupp.mem_support_iff, hD₁coe, Finsupp.sub_apply, Finsupp.smul_apply, hnot.1, hnot.2,
        smul_zero, sub_zero] at hU
      exact hU rfl
    have hD₁V : (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) V = 0 := by
      rw [hD₁coe, Finsupp.sub_apply, Finsupp.smul_apply, hDfV, smul_eq_mul, mul_one, sub_self]

    have hg₁ : P.IsGoodDiv (D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) := by
      intro U hU
      rcases hsupp U hU with h | h
      · exact hg U h
      · exact hDfgood U h

    have hadmf : P.glueData S Df ∈ GluingData.admissible S :=
      ProlongationTuple.glueData_mem_admissible_of_isGoodDiv_of_ord_eq_of_not_dvd (P := P) hqN W R hR hNR hO hWfix f h₁ h₂ hr₁ hr₂
        Df hDf hDfgood
    have ha₁ : P.glueData S D₁ ∈ GluingData.admissible S := by
      have : P.glueData S D₁ = P.glueData S D - c • P.glueData S Df := by
        rw [hD₁coe, ← Recut.glueDataHom_apply, ← Recut.glueDataHom_apply, ← Recut.glueDataHom_apply,
          map_sub, map_zsmul]
      rw [this]
      exact sub_mem ha (AddSubgroup.zsmul_mem _ hadmf c)

    have hmk₁ : Pic0.mk D₁ = Pic0.mk D := by
      apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      have : ((-D₁ + D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))))) :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) = c • Df := by
        push_cast
        rw [hD₁coe]
        abel
      rw [this]
      exact AddSubgroup.zsmul_mem _ (Divisor.mem_principal.mpr ⟨f, hf0, hDf⟩) c

    have hbad₁ : bad D₁ ⊆ (bad D).erase V := by
      intro U hU
      obtain ⟨hUsupp, hUT⟩ := (mem_bad _ U).mp hU
      have hUV : U ≠ V := by
        rintro rfl
        rw [Finsupp.mem_support_iff] at hUsupp
        exact hUsupp hD₁V
      refine Finset.mem_erase.mpr ⟨hUV, (mem_bad _ U).mpr ⟨?_, hUT⟩⟩
      rcases hsupp U hUsupp with h | h
      · exact h
      · exact absurd hUT (not_or.mpr (havoid U h hUV))
    have hcard₁ : (bad D₁).card ≤ n := by
      have := Finset.card_le_card hbad₁
      rw [Finset.card_erase_of_mem hVbad] at this
      omega
    obtain ⟨D', hg', ha', hmk', hbad'⟩ := ih D₁ hg₁ ha₁ hcard₁
    exact ⟨D', hg', ha', hmk'.trans hmk₁, hbad'⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel (solution)
