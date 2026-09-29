-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e9e4962f-a689-518a-a3b5-2e40ab28fbd9

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_self_good_admissible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

private theorem GluedHecke.core {J C Q : Type} [AddCommGroup J] [AddCommGroup C] [AddCommGroup Q]
    [Module HeckeAlg J] (S : AddSubgroup J)
    (hS : ∀ (T : HeckeAlg) (y : J), y ∈ S → T • y ∈ S)
    (comp : ↥S →+ C) (ν : ↥S →+ Q)
    (hCs : ∀ (a : ℤ) (y : J), (MvPolynomial.C a : HeckeAlg) • y = a • y)
    (hcomp : ∀ (ℓ : Nat.Primes) (x : ↥S) (hx : heckeGen ℓ • (x : J) ∈ S),
      comp x = 0 → comp ⟨heckeGen ℓ • (x : J), hx⟩ = 0)
    (hgen : ∀ (ℓ : Nat.Primes) (x : ↥S) (hx : heckeGen ℓ • (x : J) ∈ S),
      comp x = 0 → ν x = 0 → ν ⟨heckeGen ℓ • (x : J), hx⟩ = 0) :
    ∀ (T : HeckeAlg) (x : ↥S), comp x = 0 → ν x = 0 →
      ∀ (hTx : T • (x : J) ∈ S), ν ⟨T • (x : J), hTx⟩ = 0 := by
  intro T
  induction T using MvPolynomial.induction_on with
  | C a =>
    intro x h0 hν hTx

    have hx' : (⟨(MvPolynomial.C a : HeckeAlg) • (x : J), hTx⟩ : ↥S) = a • x :=
      Subtype.ext ((hCs a (x : J)).trans (map_zsmul S.subtype a x).symm)
    rw [hx', map_zsmul, hν, smul_zero]
  | add p p' hp hp' =>
    intro x h0 hν hTx
    have hpx := hS p (x : J) x.2
    have hp'x := hS p' (x : J) x.2
    have hsum : (⟨(p + p') • (x : J), hTx⟩ : ↥S)
        = ⟨p • (x : J), hpx⟩ + ⟨p' • (x : J), hp'x⟩ := by
      apply Subtype.ext
      show (p + p') • (x : J) = p • (x : J) + p' • (x : J)
      exact add_smul p p' (x : J)
    rw [hsum, map_add, hp x h0 hν hpx, hp' x h0 hν hp'x, add_zero]
  | mul_X p ℓ hp =>
    intro x h0 hν hTx
    have hyin : heckeGen ℓ • (x : J) ∈ S := hS (heckeGen ℓ) (x : J) x.2
    have hcy : comp ⟨heckeGen ℓ • (x : J), hyin⟩ = 0 := hcomp ℓ x hyin h0
    have hνy : ν ⟨heckeGen ℓ • (x : J), hyin⟩ = 0 := hgen ℓ x hyin h0 hν
    have hpmem : p • (heckeGen ℓ • (x : J)) ∈ S := hS p (heckeGen ℓ • (x : J)) hyin
    have hfinal := hp ⟨heckeGen ℓ • (x : J), hyin⟩ hcy hνy hpmem
    have hid : (⟨(p * MvPolynomial.X ℓ) • (x : J), hTx⟩ : ↥S)
        = ⟨p • (heckeGen ℓ • (x : J)), hpmem⟩ := by
      apply Subtype.ext
      show (p * MvPolynomial.X ℓ) • (x : J) = p • (heckeGen ℓ • (x : J))
      exact mul_smul p (MvPolynomial.X ℓ) (x : J)
    rw [hid]
    exact hfinal

private theorem GluedHecke.transport₂ {α : Sort*} {P : α → Prop} {Q : ∀ a, P a → Prop} {a b : α}
    (h : a = b) (ha : P a) (H : ∀ hb : P b, Q b hb) : Q a ha := by subst h; exact H ha

private theorem GluedHecke.heckeGen_smul_mk (M : ℕ) [NeZero M]
    (hcomm : HeckeOperatorsCommuteBar M) (ℓ : Nat.Primes) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∀ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * ℓ))]
      (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
        (heckeBetaBar (AlgebraicClosure ℚ) M ℓ) hβ)
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ))
      (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ) hfin)
      (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M)))),
        (letI := heckeModuleBar M; heckeGen ℓ • Pic0.mk E)
          = Pic0.mk (Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) M ℓ)
              (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ) hβ hα hFI E) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  intro hα hβ _ hFI hfin hN E
  letI := heckeModuleBar M
  rw [heckeModuleBar_heckeGen_smul hcomm ℓ, heckeOperatorBar_apply]
  have hOA := heckeOperatorAlong_eq hα hβ hFI hfin hN
  rw [hOA]
  rfl

private theorem GluedHecke.genLeg (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
    ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
      ∀ (x : ↥(inertiaInvariants A (N * q)))
        (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
        comp x = 0 → comp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ = 0 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp
  have _ := hW; have _ := hstab; have _ := hsurj; have _ := hsp; have _ := e
  intro ℓ hℓq x hx hcomp
  have hcommNq := ModularCurve.heckeOperatorsCommuteBar (N * q)
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hin_up := ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) (N * q) (ℓ : ℕ)
  obtain ⟨hαℓ, hβℓ, _, hfin_up, hFI_up, hN_up⟩ := hin_up
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * (ℓ : ℕ))

  have hgood_x : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (x : JZero (N * q)) := (hker x).1 hcomp
  have hMplus := ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hNV hO ℓ hℓq hαℓ hβℓ
    (x : JZero (N * q)) hgood_x
  obtain ⟨D, hgoodD, hadmD, hmkD, hgoodD', hadmD', hfst, hsnd⟩ := hMplus
  have _ := hgoodD; have _ := hadmD; have _ := hfst; have _ := hsnd

  let D_Tℓ := Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβℓ hαℓ hFI_up D
  have hD_Tℓ_coe : (D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = heckeDivBar hαℓ hβℓ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    Pic0.coe_degZeroCorrespondence _ _ _ _ _ D
  have hmk_Tℓ : Pic0.mk D_Tℓ = heckeGen ℓ • (x : JZero (N * q)) :=
    (GluedHecke.heckeGen_smul_mk (N * q) hcommNq ℓ hαℓ hβℓ hFI_up hfin_up hN_up D).symm.trans
      (congrArg (heckeGen ℓ • ·) hmkD)

  have hgood_Tℓ : P.IsGoodDiv
      (D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    hD_Tℓ_coe ▸ hgoodD'
  have hadm_Tℓ : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D_Tℓ
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) := by
    rw [show P.glueData _ (D_Tℓ : Divisor _ _) = P.glueData _ (heckeDivBar hαℓ hβℓ ↑D) from
      congrArg (P.glueData _) hD_Tℓ_coe]
    exact hadmD'

  have hgood_Tx : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (heckeGen ℓ • (x : JZero (N * q))) := ⟨D_Tℓ, hgood_Tℓ, hadm_Tℓ, hmk_Tℓ⟩
  exact (hker ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩).2 hgood_Tx

private theorem GluedHecke.qLeg (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
    ∀ (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen (⟨q, hq⟩ : Nat.Primes) • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → comp ⟨heckeGen (⟨q, hq⟩ : Nat.Primes) • (x : JZero (N * q)), hx⟩ = 0 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp
  have _ := hW; have _ := hstab; have _ := hsurj; have _ := hsp; have _ := e
  intro x hx hcomp
  have hcommNq := ModularCurve.heckeOperatorsCommuteBar (N * q)
  have hin_q := ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) (N * q) q
  obtain ⟨hαq, hβq, _, hfin_q, hFI_q, hN_q⟩ := hin_q
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * q)
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (modularFunctionFieldBar ((N * q) * ((⟨q, hq⟩ : Nat.Primes) : ℕ))) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * q)

  have hgood_x : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (x : JZero (N * q)) := (hker x).1 hcomp
  have hMq := ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_self_good_admissible N q hq hqN A hA W hW data hKr hα hβ P hαq hβq (x : JZero (N * q)) hgood_x
  obtain ⟨D, hgoodD, hadmD, hmkD, hgoodD', hadmD'⟩ := hMq
  have _ := hgoodD; have _ := hadmD

  let D_Tq := Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) (N * q) q)
      (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) q) hβq hαq hFI_q D
  have hD_Tq_coe : (D_Tq : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = heckeDivBar hαq hβq (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    Pic0.coe_degZeroCorrespondence _ _ _ _ _ D
  have hmk_Tq : Pic0.mk D_Tq = heckeGen (⟨q, hq⟩ : Nat.Primes) • (x : JZero (N * q)) :=
    (GluedHecke.heckeGen_smul_mk (N * q) hcommNq ⟨q, hq⟩ hαq hβq hFI_q hfin_q hN_q D).symm.trans
      (congrArg (heckeGen (⟨q, hq⟩ : Nat.Primes) • ·) hmkD)
  have hgood_Tq : P.IsGoodDiv
      (D_Tq : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    hD_Tq_coe ▸ hgoodD'
  have hadm_Tq : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D_Tq
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) := by
    rw [show P.glueData _ (D_Tq : Divisor _ _) = P.glueData _ (heckeDivBar hαq hβq ↑D) from
      congrArg (P.glueData _) hD_Tq_coe]
    exact hadmD'
  have hgood_Tx : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (heckeGen (⟨q, hq⟩ : Nat.Primes) • (x : JZero (N * q))) := ⟨D_Tq, hgood_Tq, hadm_Tq, hmk_Tq⟩
  exact (hker ⟨heckeGen (⟨q, hq⟩ : Nat.Primes) • (x : JZero (N * q)), hx⟩).2 hgood_Tx

private theorem GluedHecke.hgen (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
    ∀ (ℓ : Nat.Primes) (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
      comp x = 0 → comp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ = 0 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp
  have _ := hW; have _ := hstab; have _ := hsurj; have _ := hsp; have _ := e
  have hQc := GluedHecke.qLeg N q hq hqN A hA W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp
  have hGc := GluedHecke.genLeg N q hq hqN A hA W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp
  intro ℓ x hx h0
  by_cases hlq : (ℓ : ℕ) = q
  · exact GluedHecke.transport₂
      (P := fun m : Nat.Primes =>
        heckeGen m • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q))
      (Q := fun (m : Nat.Primes)
          (hm : heckeGen m • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)) =>
        comp ⟨heckeGen m • (x : JZero (N * q)), hm⟩ = 0)
      (Subtype.ext hlq) hx (fun hb => hQc x hb h0)
  · exact hGc ℓ hlq x hx h0

theorem solution (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
            (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 → comp ⟨T • (x : JZero (N * q)), hx⟩ = 0) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp
  have _ := hW; have _ := hstab; have _ := hsurj; have _ := hsp; have _ := e

  haveI hSMC : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg
      (JZero (N * q)) :=
    ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar (N * q) (ModularCurve.heckeOperatorsCommuteBar (N * q))
  have hmem : ∀ (T : HeckeAlg) (y : JZero (N * q)), y ∈ inertiaInvariants A (N * q) →
      T • y ∈ inertiaInvariants A (N * q) := by
    intro T y hy σ hσ
    have hc := smul_comm σ T y
    rw [hc, hy σ hσ]

  have hG := GluedHecke.hgen N q hq hqN A hA W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp

  have hCs : ∀ (a : ℤ) (y : JZero (N * q)), (MvPolynomial.C a : HeckeAlg) • y = a • y :=
    fun a y => heckeModuleBar_C_smul a y

  intro T x hx h0
  exact GluedHecke.core (J := JZero (N * q)) (S := inertiaInvariants A (N * q)) hmem comp comp
    hCs hG (fun ℓ y hy hy0 _ => hG ℓ y hy hy0) T x h0 h0 hx

end

end S_ModularCurve_PlaceSpecialization_componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_componentMap_heckeAlg_smul_eq_zero_of_eq_zero_of_isModel (solution)
