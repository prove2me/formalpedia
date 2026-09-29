-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/00636198-5d1e-5037-8781-6bb37044b22f

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_mem_closure_redRestrict
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level
import Theorems.Thm_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Definitions.Def_ModularCurve_NodeDescentTower
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_ModularCurve_CharPModel_exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
import Theorems.Thm_ModularCurve_exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~jBar ModularCurve.NodeLocalized"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace Ws18Sep2Alt

theorem isIntegral_of_subring_le {L : Type*} [CommRing L] {S T : Subring L} (h : S ≤ T) {x : L}
    (hx : IsIntegral ↥S x) : IsIntegral ↥T x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Subring.inclusion h), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap (↥T) L).comp (Subring.inclusion h) = algebraMap (↥S) L := RingHom.ext fun _ => rfl
  rw [this]
  exact hpx

variable (M : ℕ) [NeZero M] (A : ValuationSubring (AlgebraicClosure ℚ))

theorem fieldOver_mono {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) : fieldOver M K₁ ≤ fieldOver M K₂ := by
  unfold fieldOver
  refine Subfield.closure_mono (Set.union_subset_union_left _ ?_)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨(c : AlgebraicClosure ℚ), h c.2⟩, rfl⟩

theorem jRing_mono {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) : jRing A K₁ ≤ jRing A K₂ := by
  unfold jRing
  refine Subring.closure_mono (Set.union_subset_union_left _ ?_)
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨(c : AlgebraicClosure ℚ), c.2.1, h c.2.2⟩, rfl⟩

theorem jIntegralClosure_mono {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) :
    jIntegralClosure M A K₁ ≤ jIntegralClosure M A K₂ :=
  fun _ hx => ⟨fieldOver_mono M h hx.1, isIntegral_of_subring_le (jRing_mono A h) hx.2⟩

abbrev SubNF (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Type :=
  {K₀ : IntermediateField ℚ (AlgebraicClosure ℚ) // K₀ ≤ K ∧ FiniteDimensional ℚ ↥K₀}

scoped instance (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Nonempty (SubNF K) :=
  ⟨⟨⊥, bot_le, by infer_instance⟩⟩

theorem directed_subNF (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Directed (· ≤ ·) (fun i : SubNF K => (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) := by
  rintro ⟨K₁, h₁, fd₁⟩ ⟨K₂, h₂, fd₂⟩
  haveI := fd₁; haveI := fd₂
  exact ⟨⟨K₁ ⊔ K₂, sup_le h₁ h₂, IntermediateField.finiteDimensional_sup K₁ K₂⟩, le_sup_left, le_sup_right⟩

theorem exists_subNF_mem {K : IntermediateField ℚ (AlgebraicClosure ℚ)} {c : AlgebraicClosure ℚ} (hc : c ∈ K) :
    ∃ i : SubNF K, c ∈ (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
  refine ⟨⟨IntermediateField.adjoin ℚ {c}, IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hc),
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)⟩, ?_⟩
  exact IntermediateField.mem_adjoin_simple_self ℚ c

theorem fieldOver_le_iSup (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    fieldOver M K ≤ ⨆ i : SubNF K, fieldOver M (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
  unfold fieldOver
  rw [Subfield.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · obtain ⟨i, hi⟩ := exists_subNF_mem (K := K) c.2
    exact le_iSup (fun i : SubNF K => fieldOver M (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) i
      (Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), hi⟩, rfl⟩))
  · obtain ⟨i⟩ := (inferInstance : Nonempty (SubNF K))
    exact le_iSup (fun i : SubNF K => fieldOver M (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) i
      (Subfield.subset_closure (Or.inr hx))

theorem jRing_le_iSup (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ ⨆ i : SubNF K, jRing A (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ)) := by
  unfold jRing
  rw [Subring.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · obtain ⟨i, hi⟩ := exists_subNF_mem (K := K) c.2.2
    exact le_iSup (fun i : SubNF K => jRing A (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) i
      (Subring.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.1, hi⟩, rfl⟩))
  · obtain ⟨i⟩ := (inferInstance : Nonempty (SubNF K))
    exact le_iSup (fun i : SubNF K => jRing A (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) i
      (Subring.subset_closure (Or.inr hx))

theorem isIntegral_of_coeff_mem {L : Type*} [CommRing L] [Nontrivial L] {S T : Subring L} (h : T ≤ S) {x : L}
    (p : Polynomial ↥S) (hp : p.Monic) (hpx : Polynomial.eval₂ (algebraMap ↥S L) x p = 0)
    (hcoef : ∀ i, ((p.coeff i : ↥S) : L) ∈ T) : IsIntegral ↥T x := by
  classical
  let f : ↥T →+* ↥S := Subring.inclusion h
  have hlifts : p ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hcoef i⟩, Subtype.ext rfl⟩
  obtain ⟨r, hrp, -, hrmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hp
  refine ⟨r, hrmonic, ?_⟩
  have hcomp : (algebraMap ↥S L).comp f = algebraMap ↥T L := RingHom.ext fun _ => rfl
  rw [← hcomp, ← Polynomial.eval₂_map, hrp]
  exact hpx

theorem exists_subNF_mem_jIntegralClosure {K : IntermediateField ℚ (AlgebraicClosure ℚ)} {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ jIntegralClosure M A K) :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₀), K₀ ≤ K ∧ x ∈ jIntegralClosure M A K₀ := by
  classical
  obtain ⟨hxf, hxi⟩ := hx

  have hdirF : Directed (· ≤ ·) (fun i : SubNF K => fieldOver M (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) :=
    fun i j => by
      obtain ⟨l, hil, hjl⟩ := directed_subNF K i j
      exact ⟨l, fieldOver_mono M hil, fieldOver_mono M hjl⟩
  obtain ⟨i₁, hi₁⟩ := (Subfield.mem_iSup_of_directed hdirF).mp (fieldOver_le_iSup M K hxf)

  obtain ⟨p, hp, hpx⟩ := hxi
  have hdirR : Directed (· ≤ ·) (fun i : SubNF K => jRing A (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ))) :=
    fun i j => by
      obtain ⟨l, hil, hjl⟩ := directed_subNF K i j
      exact ⟨l, jRing_mono A hil, jRing_mono A hjl⟩
  have hcoef : ∀ n : ℕ, ∃ i : SubNF K, ((p.coeff n : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ jRing A (i.1 : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    fun n => (Subring.mem_iSup_of_directed hdirR).mp (jRing_le_iSup A K (p.coeff n).2)
  choose ι hι using hcoef

  let K₁ : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    (i₁.1 : IntermediateField ℚ (AlgebraicClosure ℚ)) ⊔ ⨆ n : Fin (p.natDegree + 1), ((ι n).1 : IntermediateField ℚ (AlgebraicClosure ℚ))
  haveI : ∀ n : Fin (p.natDegree + 1), FiniteDimensional ℚ ↥((ι n).1 : IntermediateField ℚ (AlgebraicClosure ℚ)) := fun n => (ι n).2.2
  haveI : FiniteDimensional ℚ ↥(i₁.1 : IntermediateField ℚ (AlgebraicClosure ℚ)) := i₁.2.2
  haveI hfd2 : FiniteDimensional ℚ ↥(⨆ n : Fin (p.natDegree + 1), ((ι n).1 : IntermediateField ℚ (AlgebraicClosure ℚ))) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  haveI : FiniteDimensional ℚ ↥K₁ := IntermediateField.finiteDimensional_sup _ _
  have hK₁K : K₁ ≤ K := sup_le i₁.2.1 (iSup_le fun n => (ι n).2.1)
  refine ⟨K₁, inferInstance, hK₁K, fieldOver_mono M le_sup_left hi₁, ?_⟩
  apply isIntegral_of_coeff_mem (jRing_mono A hK₁K) p hp hpx
  intro n
  by_cases hn : n ≤ p.natDegree
  · have hle : ((ι n).1 : IntermediateField ℚ (AlgebraicClosure ℚ)) ≤ K₁ :=
      le_trans (le_iSup (fun m : Fin (p.natDegree + 1) => ((ι m).1 : IntermediateField ℚ (AlgebraicClosure ℚ))) ⟨n, Nat.lt_succ_of_le hn⟩) le_sup_right
    exact jRing_mono A hle (hι n)
  · push Not at hn
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
    exact zero_mem _

end Ws18Sep2Alt
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)

abbrev IntJ (b : ↥(modularFunctionFieldBar N)) : Prop :=
  IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) b

omit [IsAlgClosed k] [DecidableEq k] in

theorem residue₁_atkinLehnerBar_eq_residue₂ (t : ↥(modularFunctionFieldBar (N * q))) (h₂ : t ∈ R.R₂.integers)
    (h₁' : ProlongationTuple.atkinLehnerBar N q t ∈ R.R₁.integers) :
    R.residue₁ ⟨ProlongationTuple.atkinLehnerBar N q t, h₁'⟩ = R.residue₂ ⟨t, h₂⟩ := by
  rw [residue₁_apply, residue₂_apply, R.residue₂_eq t h₂]

theorem isIntegral_of_subalgebra_le {S₀ F : Type*} [CommRing S₀] [CommRing F] [Algebra S₀ F] {S T : Subalgebra S₀ F}
    (h : S ≤ T) {x : F} (hx : IsIntegral ↥S x) : IsIntegral ↥T x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap ↥T F).comp (Subalgebra.inclusion h).toRingHom = algebraMap ↥S F := RingHom.ext fun _ => rfl
  rw [this]
  exact hpx

end Ws18Sep2V3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3SERIES

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem inv_mem_of_isUnit_vs (S : ValuationSubring F) {g : F} (h : g ∈ S) (hu : IsUnit (⟨g, h⟩ : ↥S)) :
    g ≠ 0 ∧ g⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hv' : g * (v : F) = 1 := congrArg Subtype.val hv
  have hg0 : g ≠ 0 := fun h0 => by rw [h0, zero_mul] at hv'; exact zero_ne_one hv'
  exact ⟨hg0, (eq_inv_of_mul_eq_one_right hv') ▸ v.2⟩

theorem hasValue_zero_iff (v : Place K F) (g : F) :
    v.HasValue g 0 ↔ g ∈ v.toValuationSubring ∧ (g = 0 ∨ g⁻¹ ∉ v.toValuationSubring) := by
  constructor
  · rintro ⟨h, hr⟩
    rw [map_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr
    refine ⟨h, ?_⟩
    by_cases hg0 : g = 0
    · exact Or.inl hg0
    · right
      intro hinv
      exact hr (isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg0)⟩)
  · rintro ⟨h, hor⟩
    refine ⟨h, ?_⟩
    rw [map_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rcases hor with hg0 | hinv
    · exact hu.ne_zero (Subtype.ext hg0)
    · exact hinv (inv_mem_of_isUnit_vs _ h hu).2

theorem hasValue_zero_map_iff (v : Place K F) (w : Place K F') (φ : F →+* F') (hφ : Function.Injective φ)
    (hmem : ∀ x : F, φ x ∈ w.toValuationSubring ↔ x ∈ v.toValuationSubring) (g : F) :
    w.HasValue (φ g) 0 ↔ v.HasValue g 0 := by
  rw [hasValue_zero_iff, hasValue_zero_iff, hmem, map_eq_zero_iff φ hφ, ← map_inv₀, hmem]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

section Tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem exists_mem_integersFst_coe_residue₁_eq (f : ↥(modularFunctionFieldBar (N * q))) (y' : LaurentSeries A)
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y') :
    ∃ h : f ∈ R.R₁.integers, ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = coeffMap red y' := by
  obtain ⟨fv, hfv⟩ := f
  change fv = coeffMap A.subtype y' at hf
  subst hf
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y' hfv
  refine ⟨h, ?_⟩
  rw [residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap,
    show R.redBar.comp (IsLocalRing.residue ↥A) = red from RingHom.ext R.redBar_residue]

theorem residueFst_congr {f f' : ↥(modularFunctionFieldBar (N * q))} (hf : f ∈ R.R₁.integers)
    (hf' : f' ∈ R.R₁.integers) (h : f = f') : R.R₁.residue ⟨f, hf⟩ = R.R₁.residue ⟨f', hf'⟩ := by
  subst h; rfl

theorem atkinLehnerBar_heckeAlphaBar (hqN : ¬ q ∣ N) (g : ↥(modularFunctionFieldBar N)) :
    atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q g) = heckeBetaBar (AlgebraicClosure ℚ) N q g ∧
      atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q g) = heckeAlphaBar (AlgebraicClosure ℚ) N q g := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  have hσ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨h1, h2⟩ := ModularCurve.geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ
  exact ⟨AlgHom.congr_fun h1 g, AlgHom.congr_fun h2 g⟩

theorem residues_pullbacks (hqN : ¬ q ∣ N) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (y : LaurentSeries ↥(coeffSubring A K)) (b : ↥(modularFunctionFieldBar N)) (bbar : ↥(modularFunctionFieldC k N))
    (hby : (b : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (coeffSubring A K).subtype y)
    (hred : coeffMap (redRestrict red K) y = (bbar : LaurentSeries k)) :
    ∃ (hα₁ : heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₁.integers)
      (hα₂ : heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers)
      (hβ₁ : heckeBetaBar (AlgebraicClosure ℚ) N q b ∈ R.R₁.integers)
      (hβ₂ : heckeBetaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers),
      R.residue₁ ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, hα₁⟩ = bbar ∧
      R.residue₂ ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, hα₂⟩ = frobeniusGeomLevel k N data hKr bbar ∧
      R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, hβ₁⟩ = frobeniusGeomLevel k N data hKr bbar ∧
      R.residue₂ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, hβ₂⟩ = bbar := by
  classical
  set y' : LaurentSeries A :=
    coeffMap (Subring.inclusion inf_le_left : ↥(coeffSubring A K) →+* A) y with hy'
  have hαcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q b : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y' := by
    rw [coe_heckeAlphaBar, hby, hy', coeffMap_coeffMap]; rfl
  have hβcoe : ((heckeBetaBar (AlgebraicClosure ℚ) N q b : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qExpand A q y') := by
    rw [coe_heckeBetaBar, hby, hy', coeffMap_qExpand, coeffMap_coeffMap]; rfl
  have hredy : coeffMap red y' = (bbar : LaurentSeries k) := by
    rw [hy', coeffMap_coeffMap, ← hred]; rfl
  obtain ⟨hα1, hαres⟩ := exists_mem_integersFst_coe_residue₁_eq R _ _ hαcoe
  obtain ⟨hβ1, hβres⟩ := exists_mem_integersFst_coe_residue₁_eq R _ _ hβcoe
  obtain ⟨hALα, hALβ⟩ := atkinLehnerBar_heckeAlphaBar hqN b
  have hα2 : heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hALα]; exact hβ1
  have hβ2 : heckeBetaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hALβ]; exact hα1

  have hresα : R.residue₁ ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, hα1⟩ = bbar :=
    Subtype.ext (hαres.trans hredy)
  have hresβ : R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, hβ1⟩ = frobeniusGeomLevel k N data hKr bbar := by
    apply Subtype.ext
    rw [hβres, frobeniusGeomLevel_apply_coe, coeffSemilinearAut.coeffMap_qExpand, hredy]
  refine ⟨hα1, hα2, hβ1, hβ2, hresα, ?_, hresβ, ?_⟩
  · rw [residue₂_apply, R.residue₂_eq, residueFst_congr R _ hβ1 hALα, ← residue₁_apply]
    exact hresβ
  · rw [residue₂_apply, R.residue₂_eq, residueFst_congr R _ hα1 hALβ, ← residue₁_apply]
    exact hresα

end Tuple
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

end Ws18Sep2V3SERIES
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)

include hqN in

theorem hasValue_frob_smul_iff (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (g : ↥(modularFunctionFieldC k N)) :
    (arithFrobC q k N • v).HasValue (frobeniusGeomLevel k N data hKr g) (0 : k) ↔ v.HasValue g (0 : k) := by
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr v]
  refine Ws18Sep2V3SERIES.hasValue_zero_map_iff v _ (frobeniusGeomLevel k N data hKr).toRingHom
    (frobeniusGeomLevel_injective k N data hKr) (fun x => ?_) g
  have hfix := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr v hv
  have h := mem_frobOnPlacesGeomLevel_iff k N data hKr (frobOnPlacesGeomLevel k N data hKr v) x
  rw [hfix] at h
  exact h.symm

omit [DecidableEq k] in

theorem hasValue_frob_iff_smul (v : Place k (modularFunctionFieldC k N)) (g : ↥(modularFunctionFieldC k N)) :
    v.HasValue (frobeniusGeomLevel k N data hKr g) (0 : k) ↔ (arithFrobC q k N • v).HasValue g (0 : k) := by
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr v]
  exact Ws18Sep2V3SERIES.hasValue_zero_map_iff _ v (frobeniusGeomLevel k N data hKr).toRingHom
    (frobeniusGeomLevel_injective k N data hKr) (fun x => (mem_frobOnPlacesGeomLevel_iff k N data hKr v x).symm) g

include hqN in

theorem hasValue_residue_heckeAlphaBar (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (y : LaurentSeries ↥(coeffSubring A K)) (b : ↥(modularFunctionFieldBar N)) (bbar : ↥(modularFunctionFieldC k N))
    (hby : (b : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (coeffSubring A K).subtype y)
    (hred : coeffMap (redRestrict red K) y = (bbar : LaurentSeries k))
    (hbK : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver N K) (hint : IntJ b) :
    ∃ (h₁ : heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₁.integers) (h₂ : heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers),
      R.residue₁ ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, h₁⟩ = bbar ∧
      ((arithFrobC q k N • v).HasValue (R.residue₂ ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ↔
        v.HasValue bbar (0 : k)) := by
  obtain ⟨hα₁, hα₂, -, -, h1, h2, -, -⟩ :=
    Ws18Sep2V3SERIES.residues_pullbacks R hqN K y b bbar hby hred
  refine ⟨hα₁, hα₂, h1, ?_⟩
  rw [h2]
  exact hasValue_frob_smul_iff hqN v hv bbar

include hqN in

theorem hasValue_residue_heckeBetaBar (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (y : LaurentSeries ↥(coeffSubring A K)) (b : ↥(modularFunctionFieldBar N)) (bbar : ↥(modularFunctionFieldC k N))
    (hby : (b : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (coeffSubring A K).subtype y)
    (hred : coeffMap (redRestrict red K) y = (bbar : LaurentSeries k))
    (hbK : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver N K) (hint : IntJ b) :
    ∃ (h₁ : heckeBetaBar (AlgebraicClosure ℚ) N q b ∈ R.R₁.integers) (h₂ : heckeBetaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers),
      R.residue₂ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, h₂⟩ = bbar ∧
      (v.HasValue (R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ↔
        (arithFrobC q k N • v).HasValue bbar (0 : k)) := by
  obtain ⟨-, -, hβ₁, hβ₂, -, -, h3, h4⟩ :=
    Ws18Sep2V3SERIES.residues_pullbacks R hqN K y b bbar hby hred
  refine ⟨hβ₁, hβ₂, h4, ?_⟩
  rw [h3]
  exact hasValue_frob_iff_smul v bbar

end Ws18Sep2V3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3

private theorem _root_.AlgebraicCurve.Place.HasValue.add' {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) : v.HasValue (f + g) (a + b) := by
  obtain ⟨h1, r1⟩ := hf
  obtain ⟨h2, r2⟩ := hg
  refine ⟨add_mem h1 h2, ?_⟩
  have : (⟨f + g, add_mem h1 h2⟩ : ↥v.toValuationSubring) = ⟨f, h1⟩ + ⟨g, h2⟩ := rfl
  rw [this, map_add, r1, r2, map_add]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.AlgebraicCurve.Place.HasValue.add'" "AlgebraicCurve.Place.HasValue.add'"
private theorem _root_.AlgebraicCurve.Place.HasValue.sub'' {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) : v.HasValue (f - g) (a - b) := by
  obtain ⟨h1, r1⟩ := hf
  obtain ⟨h2, r2⟩ := hg
  refine ⟨sub_mem h1 h2, ?_⟩
  have : (⟨f - g, sub_mem h1 h2⟩ : ↥v.toValuationSubring) = ⟨f, h1⟩ - ⟨g, h2⟩ := rfl
  rw [this, map_sub, r1, r2, map_sub]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.AlgebraicCurve.Place.HasValue.sub''" "AlgebraicCurve.Place.HasValue.sub''"

theorem exists_numberField_pow_sq_subset_range' {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} [IsAlgClosed k] :
    ∃ (K₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₁),
      ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (redRestrict red K₁) := by
  classical
  have hq2 : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero k two_ne_zero (Fact.out : q.Prime).one_lt
  obtain ⟨K₁, hK₁fd, -, hK₁⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) (by
        intro a ha
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hq2, Polynomial.IsRoot.def] at ha
        simpa [sub_eq_zero] using ha)
  refine ⟨K₁, hK₁fd, fun a ha => hK₁ a ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hq2, Polynomial.IsRoot.def]
  simp [ha]

theorem range_redRestrict_mono' {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] {red : A →+* k}
    {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) :
    Set.range (redRestrict red K₁) ⊆ Set.range (redRestrict red K₂) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨(x : AlgebraicClosure ℚ), x.2.1, h x.2.2⟩, rfl⟩

end Ws18Sep2V3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)

include R in
omit [IsAlgClosed k] [DecidableEq k] in

theorem inv_mem_range_redRestrict (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {a : k}
    (ha : a ∈ Set.range (redRestrict red K)) : a⁻¹ ∈ Set.range (redRestrict red K) := by
  obtain ⟨x, rfl⟩ := ha
  by_cases hx : redRestrict red K x = 0
  · exact ⟨0, by rw [hx, inv_zero, map_zero]⟩
  · have hxA : IsUnit (⟨(x : AlgebraicClosure ℚ), x.2.1⟩ : ↥A) := by
      by_contra hnu
      apply hx
      have hmem : (⟨(x : AlgebraicClosure ℚ), x.2.1⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := hnu
      show red ⟨(x : AlgebraicClosure ℚ), x.2.1⟩ = 0
      rw [← R.redBar_residue, (IsLocalRing.residue_eq_zero_iff _).mpr hmem, map_zero]
    obtain ⟨u, hu⟩ := hxA
    have hx0 : (x : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply hx
      have : x = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hinvA : (x : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A) * (u : ↥A) = 1 := Units.inv_mul u
      have h2 : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) = 1 := by
        have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) h1
        simpa [hu] using this
      rw [← eq_inv_of_mul_eq_one_left h2]
      exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
    have hinvK : (x : AlgebraicClosure ℚ)⁻¹ ∈ K := inv_mem x.2.2
    refine ⟨⟨(x : AlgebraicClosure ℚ)⁻¹, hinvA, hinvK⟩, ?_⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (⟨(x : AlgebraicClosure ℚ)⁻¹, hinvA, hinvK⟩ : ↥(coeffSubring A K)) * x = 1 :=
      Subtype.ext (inv_mul_cancel₀ hx0)
    rw [this, map_one]

def redRangeSubfield (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subfield k where
  toSubring := (redRestrict red K).range
  inv_mem' _ ha := inv_mem_range_redRestrict R K ha

omit [IsAlgClosed k] [DecidableEq k] in
theorem mem_redRangeSubfield_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {a : k} :
    a ∈ redRangeSubfield R K ↔ a ∈ Set.range (redRestrict red K) :=
  RingHom.mem_range

omit [IsAlgClosed k] [DecidableEq k] in
theorem closure_range_redRestrict_le (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subfield.closure (Set.range (redRestrict red K)) ≤ redRangeSubfield R K :=
  Subfield.closure_le.mpr fun _ ha => (mem_redRangeSubfield_iff R K).mpr ha

omit [IsAlgClosed k] [DecidableEq k] in

theorem coe_mem_fieldRange_coeffMap_of_mem_closure (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : ↥(modularFunctionFieldC k N)}
    (hx : x ∈ Subfield.closure (Set.range (fun c : ↥(Subfield.closure (Set.range (redRestrict red K))) =>
        algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))})) :
    (x : LaurentSeries k) ∈ (coeffMap (redRangeSubfield R K).subtype).fieldRange := by
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | rfl | rfl
      · have hc : (c : k) ∈ redRangeSubfield R K := closure_range_redRestrict_le R K c.2
        refine ⟨HahnSeries.single 0 ⟨(c : k), hc⟩, ?_⟩
        rw [coeffMap_single]
        show HahnSeries.single 0 (c : k) = ((algebraMap k ↥(modularFunctionFieldC k N) (c : k) : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        rw [← algebraMap_laurentSeries_eq_single]; rfl
      · exact ⟨jqModC ↥(redRangeSubfield R K), by rw [coe_jGeomGen]; exact coeffSemilinearAut.coeffMap_jqModC _⟩
      · exact ⟨jqNModC ↥(redRangeSubfield R K) N, by rw [coe_jNGeomGen]; exact coeffSemilinearAut.coeffMap_jqNModC _ N⟩
  | one => rw [OneMemClass.coe_one]; exact one_mem _
  | add x y _ _ hx hy => rw [AddMemClass.coe_add]; exact add_mem hx hy
  | neg x _ hx => rw [NegMemClass.coe_neg]; exact neg_mem hx
  | inv x _ hx => rw [IntermediateField.coe_inv]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [MulMemClass.coe_mul]; exact mul_mem hx hy

omit [IsAlgClosed k] [DecidableEq k] in

theorem exists_coeffMap_redRestrict_eq_of_mem_fieldRange (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {s : LaurentSeries k} (hs : s ∈ (coeffMap (redRangeSubfield R K).subtype).fieldRange) :
    ∃ h₀ : LaurentSeries ↥(coeffSubring A K), coeffMap (redRestrict red K) h₀ = s := by
  classical
  obtain ⟨h, rfl⟩ := RingHom.mem_fieldRange.mp hs
  have hcoef : ∀ n : ℤ, ∃ c : ↥(coeffSubring A K), redRestrict red K c = (h.coeff n : k) :=
    fun n => (mem_redRangeSubfield_iff R K).mp (h.coeff n).2
  choose c hc using hcoef
  let c' : ℤ → ↥(coeffSubring A K) := fun n => if h.coeff n = 0 then 0 else c n
  have hsupp : Function.support c' ⊆ Function.support h.coeff := by
    intro n hn
    simp only [Function.mem_support, ne_eq, c'] at hn ⊢
    intro h0; exact hn (by rw [if_pos h0])
  refine ⟨⟨c', h.isPWO_support'.mono hsupp⟩, ?_⟩
  ext n
  rw [coeffMap_coeff, coeffMap_coeff]
  show redRestrict red K (c' n) = _
  simp only [c']
  split_ifs with h0
  · rw [map_zero, h0]; rfl
  · exact hc n

include hqN in

theorem exists_coeffMap_eq_residue₁ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K)
    (h₁ : t ∈ R.R₁.integers) :
    ∃ h₀ : LaurentSeries ↥(coeffSubring A K),
      coeffMap (redRestrict red K) h₀ = ((R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) := by
  have hmem : t ∈ R.nodeIntegersOver K v :=
    ⟨(R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K v hv t ht).1, ht.1⟩
  have hcl := (R.nodeResidue_mem_closure_redRestrict hqN K v ⟨t, hmem⟩).1
  exact exists_coeffMap_redRestrict_eq_of_mem_fieldRange R K (coe_mem_fieldRange_coeffMap_of_mem_closure R K hcl)

include hqN in

theorem exists_coeffMap_eq_residue₂ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K)
    (h₂ : t ∈ R.R₂.integers) :
    ∃ h₀ : LaurentSeries ↥(coeffSubring A K),
      coeffMap (redRestrict red K) h₀ = ((R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) := by
  have hmem : t ∈ R.nodeIntegersOver K v :=
    ⟨(R.mem_nodeIntegers_and_residue_mem_of_mem_jIntegralClosure hqN K v hv t ht).1, ht.1⟩
  have hcl := (R.nodeResidue_mem_closure_redRestrict hqN K v ⟨t, hmem⟩).2
  exact exists_coeffMap_redRestrict_eq_of_mem_fieldRange R K (coe_mem_fieldRange_coeffMap_of_mem_closure R K hcl)

end Ws18Sep2V3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3

section AtkinLehner

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)

theorem coe_jFun : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
    jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
  exact coeffSemilinearAut.coeffMap_jqModC _

include hqN in

theorem atkinLehnerBar_heckeAlphaBar' (g : ↥(modularFunctionFieldBar N)) :
    atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q g) = heckeBetaBar (AlgebraicClosure ℚ) N q g ∧
      atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q g) = heckeAlphaBar (AlgebraicClosure ℚ) N q g := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  have hσ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨h1, h2⟩ := ModularCurve.geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q _ hσ
  exact ⟨AlgHom.congr_fun h1 g, AlgHom.congr_fun h2 g⟩

include hqN in

theorem coe_atkinLehnerBar_jFun :
    ((atkinLehnerBar N q (jFun N q) : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  let jN : ↥(modularFunctionFieldBar N) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
  have hα : heckeAlphaBar (AlgebraicClosure ℚ) N q jN = jFun N q := Subtype.ext (coe_heckeAlphaBar N q jN)
  rw [← hα, (atkinLehnerBar_heckeAlphaBar' hqN jN).1, coe_heckeBetaBar]
  show qExpand (AlgebraicClosure ℚ) q (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ)) = _
  rw [coeffSemilinearAut.coeffMap_jqModC, qExpand_congr (one_mul q).symm]
  rfl

include hqN in

theorem atkinLehnerBar_atkinLehnerBar (x : ↥(modularFunctionFieldBar (N * q))) :
    atkinLehnerBar N q (atkinLehnerBar N q x) = x := by
  have h : atkinLehnerInvolutionFull N q * atkinLehnerInvolutionFull N q = 1 :=
    AlgEquiv.ext fun y => ModularCurve.atkinLehnerInvolutionFull_apply_apply N q hqN y
  have h2 := congrArg (fun σ => geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ x) h
  simp only [map_mul, map_one, AlgEquiv.mul_apply, AlgEquiv.one_apply] at h2
  exact h2

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem jRing_subset_bar (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∀ x ∈ jRing A K, x ∈ modularFunctionFieldBar (N * q) := by
  intro x hx
  have hle : jRing A K ≤ (modularFunctionFieldBar (N * q)).toSubfield.toSubring := by
    unfold jRing
    rw [Subring.closure_le]
    rintro y (⟨c, rfl⟩ | rfl)
    · exact (modularFunctionFieldBar (N * q)).algebraMap_mem (c : AlgebraicClosure ℚ)
    · show jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar (N * q)
      rw [← coe_jFun (q := q) (N := N)]
      exact (jFun N q).2
  exact hle hx

include hqN in

theorem isIntegral_jRing_atkinLehnerBar (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (t : ↥(modularFunctionFieldBar (N * q))) (ht : IsIntegral ↥(jRing A K) (t : LaurentSeries (AlgebraicClosure ℚ))) :
    IsIntegral ↥(jRing A K)
      ((atkinLehnerBar N q t : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  classical

  let incl : ↥(jRing A K) →+* ↥(modularFunctionFieldBar (N * q)) :=
    { toFun := fun c => ⟨(c : LaurentSeries (AlgebraicClosure ℚ)), jRing_subset_bar A K c c.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let ψ : ↥(jRing A K) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp
      ((atkinLehnerBar N q).toAlgHom.toRingHom.comp incl)
  have hψ_apply : ∀ c : ↥(jRing A K), ψ c = ((atkinLehnerBar N q (incl c) : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) := fun _ => rfl

  obtain ⟨p, hp, hpt⟩ := ht
  have h1 : (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp incl =
      algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) := RingHom.ext fun _ => rfl
  have h2 : Polynomial.eval₂ incl t p = 0 := by
    apply (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [Polynomial.hom_eval₂, h1, map_zero]
    exact hpt
  have h3 : Polynomial.eval₂ ((atkinLehnerBar N q).toAlgHom.toRingHom.comp incl) (atkinLehnerBar N q t) p = 0 := by
    have := Polynomial.hom_eval₂ p incl (atkinLehnerBar N q).toAlgHom.toRingHom t
    rw [h2, map_zero] at this
    exact this.symm
  have hψ : Polynomial.eval₂ ψ ((atkinLehnerBar N q t : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) p = 0 := by
    have := Polynomial.hom_eval₂ p ((atkinLehnerBar N q).toAlgHom.toRingHom.comp incl)
      (algebraMap ↥(modularFunctionFieldBar (N * q)) (LaurentSeries (AlgebraicClosure ℚ))) (atkinLehnerBar N q t)
    rw [h3, map_zero] at this
    exact this.symm

  have hgen : ∀ c : ↥(jRing A K), IsIntegral ↥(jRing A K) (ψ c) := by
    rintro ⟨c, hc⟩
    induction hc using Subring.closure_induction with
    | mem x hx =>
        rcases hx with ⟨a, rfl⟩ | rfl
        ·
          have hincl : incl ⟨CharPReduction.constSeries (coeffSubring A K) a, Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩ =
              algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :=
            Subtype.ext rfl
          rw [hψ_apply, hincl, AlgEquiv.commutes]
          have hcst : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) :
              ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
              algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ))
                ⟨CharPReduction.constSeries (coeffSubring A K) a, Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩ := rfl
          rw [hcst]
          exact isIntegral_algebraMap
        ·
          have hincl : incl ⟨jqModC (AlgebraicClosure ℚ), Subring.subset_closure (Or.inr rfl)⟩ = jFun N q :=
            Subtype.ext (coe_jFun (q := q) (N := N)).symm
          rw [hψ_apply, hincl, coe_atkinLehnerBar_jFun hqN]
          exact (NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem (q := q) A K).2.2
    | zero => rw [show (⟨0, Subring.zero_mem _⟩ : ↥(jRing A K)) = 0 from rfl, map_zero]; exact isIntegral_zero
    | one => rw [show (⟨1, Subring.one_mem _⟩ : ↥(jRing A K)) = 1 from rfl, map_one]; exact isIntegral_one
    | add x y hx hy ihx ihy =>
        rw [show (⟨x + y, Subring.add_mem _ hx hy⟩ : ↥(jRing A K)) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]
        exact ihx.add ihy
    | neg x hx ihx =>
        rw [show (⟨-x, Subring.neg_mem _ hx⟩ : ↥(jRing A K)) = -⟨x, hx⟩ from rfl, map_neg]
        exact ihx.neg
    | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, Subring.mul_mem _ hx hy⟩ : ↥(jRing A K)) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
        exact ihx.mul ihy

  let C := integralClosure ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ))
  have hψC : ∀ c, ψ c ∈ C := fun c => hgen c
  let θ : ↥(jRing A K) →+* ↥C := ψ.codRestrict C hψC
  have hcomp : (algebraMap ↥C (LaurentSeries (AlgebraicClosure ℚ))).comp θ = ψ := RingHom.ext fun _ => rfl
  have hAL : IsIntegral ↥C ((atkinLehnerBar N q t : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) :=
    ⟨p.map θ, hp.map θ, by rw [Polynomial.eval₂_map, hcomp]; exact hψ⟩
  exact isIntegral_trans _ hAL

include hqN in

theorem exists_atkinLehnerBar_mem_jIntegralClosure {k : Type*} [Field k] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (t : ↥(modularFunctionFieldBar (N * q)))
    (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K) :
    ∃ (K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K₂), K ≤ K₂ ∧
      ((atkinLehnerBar N q t : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        jIntegralClosure (N * q) A K₂ := by
  obtain ⟨K₃, hK₃, hmem, -⟩ :=
    ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq_level A red (0 : k) ⟨0, map_zero red⟩ (N * q)
      (atkinLehnerBar N q t)
  haveI := hK₃
  refine ⟨K ⊔ K₃, IntermediateField.finiteDimensional_sup K K₃, le_sup_left, ?_, ?_⟩
  · exact Ws18Sep2Alt.fieldOver_mono (N * q) le_sup_right hmem
  · exact Ws18Sep2Alt.isIntegral_of_subring_le (Ws18Sep2Alt.jRing_mono A le_sup_left)
      (isIntegral_jRing_atkinLehnerBar hqN A K t ht.2)

end AtkinLehner
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

end Ws18Sep2V3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3MEMCK

open ModularCurve.CharPModel Polynomial

local notation "Qbar" => AlgebraicClosure ℚ

section Generic

private theorem _root_.Ws18Sep2V3MEMCK.isIntegral_of_subring_le {L : Type*} [CommRing L] {S T : Subring L} (h : S ≤ T) {x : L}
    (hx : IsIntegral ↥S x) : IsIntegral ↥T x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Subring.inclusion h), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap (↥T) L).comp (Subring.inclusion h) = algebraMap (↥S) L := RingHom.ext fun _ => rfl
  rw [this]
  exact hpx

p2m_export "Ws18Sep2V3MEMCK" "isIntegral_of_subring_le"

theorem isIntegral_of_evalModularPair_eq_zero {L : Type*} [CommRing L] (S : Subring L) {x y : L} (hx : x ∈ S)
    (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic) (h : evalModularPair x y Φ = 0) : IsIntegral ↥S y := by
  let g : Polynomial ℤ →+* ↥S := Polynomial.eval₂RingHom (Int.castRingHom ↥S) ⟨x, hx⟩
  refine ⟨Φ.map g, hΦ.map g, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (↥S) L).comp g = Polynomial.eval₂RingHom (Int.castRingHom L) x := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    simp only [g, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl
  rw [hcomp]
  exact h

theorem mem_of_isIntegral_toSubring {F : Type*} [Field F] (S : ValuationSubring F) {x : F}
    (hx : IsIntegral ↥S.toSubring x) : x ∈ S := by
  have hv : S.valuation.Integers ↥S.toSubring :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => (S.valuation_le_one_iff _).mpr a.2
      exists_of_le_one := fun r hr => ⟨⟨r, (S.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have := hv.mem_of_integral hx
  rw [ValuationSubring.integer_valuation] at this
  exact this

theorem mem_of_isIntegral_subalgebra {k F : Type*} [Field k] [Field F] [Algebra k F] (S : ValuationSubring F)
    (O : Subalgebra k F) (hO : ∀ x, x ∈ O ↔ x ∈ S) {x : F} (hx : IsIntegral ↥O x) : x ∈ S := by
  have hv : S.valuation.Integers ↥O :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => (S.valuation_le_one_iff _).mpr ((hO _).mp a.2)
      exists_of_le_one := fun r hr => ⟨⟨r, (hO r).mpr ((S.valuation_le_one_iff r).mp hr)⟩, rfl⟩ }
  have := hv.mem_of_integral hx
  rw [ValuationSubring.integer_valuation] at this
  exact this

theorem isIntegral_of_subalgebra_le {k L : Type*} [CommRing k] [CommRing L] [Algebra k L] {S T : Subalgebra k L}
    (h : S ≤ T) {x : L} (hx : IsIntegral ↥S x) : IsIntegral ↥T x := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap (↥T) L).comp (Subalgebra.inclusion h).toRingHom = algebraMap (↥S) L :=
    RingHom.ext fun _ => rfl
  rw [this]
  exact hpx

end Generic
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

section Generators

variable (N q : ℕ) [NeZero N] [Fact q.Prime]

theorem coe_jBar : ((jBar N : ↥(modularFunctionFieldBar N)) : LaurentSeries Qbar) = jqModC Qbar :=
  coeffEmb_jq_eq

theorem coe_jNBar : ((jNBar N : ↥(modularFunctionFieldBar N)) : LaurentSeries Qbar) = jqNModC Qbar N := by
  change coeffEmb Qbar (qExpand ℚ N jq) = _
  rw [coeffEmb_qExpand_eq, coeffEmb_jq_eq, jqNModC]

theorem evalModularPair_jBar_jNBar (dataN : ModularPolynomialData N) :
    evalModularPair (jBar N) (jNBar N) dataN.Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldBar N).val.toRingHom (jBar N) (jNBar N) dataN.Φ
  have h1 : (modularFunctionFieldBar N).val.toRingHom (jBar N) = jqModC Qbar := coe_jBar N
  have h2 : (modularFunctionFieldBar N).val.toRingHom (jNBar N) = jqNModC Qbar N := coe_jNBar N
  rw [h1, h2, evalModularPair_jq_eq_zero Qbar dataN] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldBar N).val.toRingHom.injective).mp hval

theorem coe_jFun : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries Qbar) = jqModC Qbar :=
  coeffEmb_jq_eq

theorem coe_jQFun : ((jQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries Qbar) = jqNModC Qbar q := by
  change coeffEmb Qbar (qExpand ℚ q jq) = _
  rw [coeffEmb_qExpand_eq, coeffEmb_jq_eq, jqNModC]

theorem evalModularPair_jFun_jQFun (dataq : ModularPolynomialData q) :
    evalModularPair (jFun N q) (jQFun N q) dataq.Φ = 0 := by
  have hval := map_evalModularPair (modularFunctionFieldBar (N * q)).val.toRingHom (jFun N q) (jQFun N q) dataq.Φ
  have h1 : (modularFunctionFieldBar (N * q)).val.toRingHom (jFun N q) = jqModC Qbar := coe_jFun N q
  have h2 : (modularFunctionFieldBar (N * q)).val.toRingHom (jQFun N q) = jqNModC Qbar q := coe_jQFun N q
  rw [h1, h2, evalModularPair_jq_eq_zero Qbar dataq] at hval
  exact (map_eq_zero_iff _ (modularFunctionFieldBar (N * q)).val.toRingHom.injective).mp hval

theorem heckeAlphaBar_jBar : heckeAlphaBar Qbar N q (jBar N) = jBar (N * q) :=
  Subtype.ext (coe_heckeAlphaBar N q (jBar N))

theorem heckeBetaBar_jBar : heckeBetaBar Qbar N q (jBar N) = jQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar N q]
  change qExpand Qbar q (coeffEmb Qbar jq) = coeffEmb Qbar (qExpand ℚ q jq)
  rw [coeffEmb_qExpand_eq]

end Generators
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

section Regular

variable (N : ℕ) [NeZero N]

theorem mem_of_jBar_mem (dataN : ModularPolynomialData N) (b : ↥(modularFunctionFieldBar N))
    (hint : IsIntegral ↥(Algebra.adjoin Qbar ({jBar N, jNBar N} : Set ↥(modularFunctionFieldBar N))) b)
    (u₀ : Place Qbar ↥(modularFunctionFieldBar N)) (hj : jBar N ∈ u₀.toValuationSubring) :
    b ∈ u₀.toValuationSubring := by
  have hjN : jNBar N ∈ u₀.toValuationSubring :=
    mem_of_isIntegral_toSubring _
      (isIntegral_of_evalModularPair_eq_zero u₀.toValuationSubring.toSubring hj dataN.Φ dataN.monic
        (evalModularPair_jBar_jNBar N dataN))
  let O : Subalgebra Qbar ↥(modularFunctionFieldBar N) :=
    { carrier := u₀.toValuationSubring
      mul_mem' := fun ha hb => mul_mem ha hb
      one_mem' := one_mem _
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := u₀.algebraMap_mem' }
  have hO : ∀ x, x ∈ O ↔ x ∈ u₀.toValuationSubring := fun _ => Iff.rfl
  have hadj : Algebra.adjoin Qbar ({jBar N, jNBar N} : Set ↥(modularFunctionFieldBar N)) ≤ O := by
    refine Algebra.adjoin_le ?_
    rintro _ (rfl | rfl)
    · exact hj
    · exact hjN
  exact mem_of_isIntegral_subalgebra _ O hO (isIntegral_of_subalgebra_le hadj hint)

end Regular
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

section Transport

variable (A : ValuationSubring Qbar) (N q : ℕ) [NeZero N] [Fact q.Prime]

theorem constantsHom_mem_affineBaseFin (M : ℕ) [NeZero M] (a : A) : constantsHom M A a ∈ affineBaseFin M A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem jBar_mem_affineBaseFin (M : ℕ) [NeZero M] : jBar M ∈ affineBaseFin M A :=
  Subring.subset_closure (Or.inr rfl)

theorem heckeAlphaBar_constantsHom (a : A) :
    heckeAlphaBar Qbar N q (constantsHom N A a) = constantsHom (N * q) A a :=
  (heckeAlphaBar Qbar N q).commutes (a : Qbar)

omit [NeZero N] in
theorem heckeBetaBar_constantsHom (a : A) :
    heckeBetaBar Qbar N q (constantsHom N A a) = constantsHom (N * q) A a :=
  (heckeBetaBar Qbar N q).commutes (a : Qbar)

theorem heckeAlphaBar_mem_affineBaseFin {x : ↥(modularFunctionFieldBar N)} (hx : x ∈ affineBaseFin N A) :
    heckeAlphaBar Qbar N q x ∈ affineBaseFin (N * q) A := by
  change x ∈ Subring.closure _ at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [heckeAlphaBar_constantsHom]; exact constantsHom_mem_affineBaseFin A (N * q) a
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, heckeAlphaBar_jBar]
        exact jBar_mem_affineBaseFin A (N * q)
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem isIntegral_jQFun (dataq : ModularPolynomialData q) :
    IsIntegral ↥(affineBaseFin (N * q) A) (jQFun N q) :=
  isIntegral_of_evalModularPair_eq_zero (affineBaseFin (N * q) A) (jBar_mem_affineBaseFin A (N * q))
    dataq.Φ dataq.monic (evalModularPair_jFun_jQFun N q dataq)

theorem isIntegral_constantsHom (M : ℕ) [NeZero M] (a : A) : IsIntegral ↥(affineBaseFin M A) (constantsHom M A a) :=
  isIntegral_algebraMap (R := ↥(affineBaseFin M A)) (x := ⟨constantsHom M A a, constantsHom_mem_affineBaseFin A M a⟩)

theorem heckeBetaBar_mem_integralClosure (dataq : ModularPolynomialData q) {x : ↥(modularFunctionFieldBar N)}
    (hx : x ∈ affineBaseFin N A) :
    heckeBetaBar Qbar N q x ∈ integralClosure ↥(affineBaseFin (N * q) A) ↥(modularFunctionFieldBar (N * q)) := by
  change x ∈ Subring.closure _ at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [heckeBetaBar_constantsHom, mem_integralClosure_iff]; exact isIntegral_constantsHom A (N * q) a
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, heckeBetaBar_jBar, mem_integralClosure_iff]
        exact isIntegral_jQFun A N q dataq
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem isIntegral_heckeAlphaBar {b : ↥(modularFunctionFieldBar N)} (hb : IsIntegral ↥(affineBaseFin N A) b) :
    IsIntegral ↥(affineBaseFin (N * q) A) (heckeAlphaBar Qbar N q b) := by
  obtain ⟨p, hp, hpb⟩ := hb
  let α' : ↥(modularFunctionFieldBar N) →+* ↥(modularFunctionFieldBar (N * q)) := heckeAlphaBar Qbar N q
  let res : ↥(affineBaseFin N A) →+* ↥(affineBaseFin (N * q) A) :=
    (α'.comp (affineBaseFin N A).subtype).codRestrict _ (fun x => heckeAlphaBar_mem_affineBaseFin A N q x.2)
  refine ⟨p.map res, hp.map res, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap ↥(affineBaseFin (N * q) A) ↥(modularFunctionFieldBar (N * q))).comp res
      = α'.comp (algebraMap ↥(affineBaseFin N A) ↥(modularFunctionFieldBar N)) :=
    RingHom.ext fun _ => rfl
  have h := congrArg α' hpb
  rw [Polynomial.hom_eval₂, map_zero] at h
  rw [hcomp]
  exact h

theorem isIntegral_heckeBetaBar (dataq : ModularPolynomialData q) {b : ↥(modularFunctionFieldBar N)}
    (hb : IsIntegral ↥(affineBaseFin N A) b) :
    IsIntegral ↥(affineBaseFin (N * q) A) (heckeBetaBar Qbar N q b) := by
  obtain ⟨p, hp, hpb⟩ := hb
  let β' : ↥(modularFunctionFieldBar N) →+* ↥(modularFunctionFieldBar (N * q)) := heckeBetaBar Qbar N q
  let C := integralClosure ↥(affineBaseFin (N * q) A) ↥(modularFunctionFieldBar (N * q))
  let res : ↥(affineBaseFin N A) →+* ↥C :=
    (β'.comp (affineBaseFin N A).subtype).codRestrict C (fun x => heckeBetaBar_mem_integralClosure A N q dataq x.2)
  have hC : IsIntegral ↥C (heckeBetaBar Qbar N q b) := by
    refine ⟨p.map res, hp.map res, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥C ↥(modularFunctionFieldBar (N * q))).comp res
        = β'.comp (algebraMap ↥(affineBaseFin N A) ↥(modularFunctionFieldBar N)) :=
      RingHom.ext fun _ => rfl
    have h := congrArg β' hpb
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [hcomp]
    exact h
  exact isIntegral_trans _ hC

end Transport
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

section Tuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem mem_integersFst_of_coe_eq (f : ↥(modularFunctionFieldBar (N * q))) (y' : LaurentSeries A)
    (hf : (f : LaurentSeries Qbar) = coeffMap A.subtype y') : f ∈ R.R₁.integers := by
  obtain ⟨fv, hfv⟩ := f
  change fv = coeffMap A.subtype y' at hf
  subst hf
  exact (R.residue₁_coeffMap y' hfv).1

end Tuple
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

end Ws18Sep2V3MEMCK
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

namespace Ws18Sep2V3

open ModularCurve.CharPModel Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)

include R hqN in
omit [IsAlgClosed k] [DecidableEq k] in

theorem exists_forall_coe_heckeAlphaBar_mem_jIntegralClosure_and (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K]
    (y : LaurentSeries ↥(coeffSubring A K)) (b : ↥(modularFunctionFieldBar N))
    (hby : (b : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (coeffSubring A K).subtype y)
    (hbK : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver N K) (hint : IntJ b) :
    ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
      ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
        ((heckeAlphaBar (AlgebraicClosure ℚ) N q b : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' ∧
        ((heckeBetaBar (AlgebraicClosure ℚ) N q b : ↥(modularFunctionFieldBar (N * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' := by
  classical

  set y' : LaurentSeries A := coeffMap (Subring.inclusion inf_le_left : ↥(coeffSubring A K) →+* A) y with hy'
  have hαcoe : ((heckeAlphaBar (AlgebraicClosure ℚ) N q b : ↥(modularFunctionFieldBar (N * q))) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y' := by
    rw [coe_heckeAlphaBar, hby, hy', coeffMap_coeffMap]; rfl
  have hα1 := Ws18Sep2V3MEMCK.mem_integersFst_of_coe_eq R _ _ hαcoe
  have hloc : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := by
    have := (R.mem_integersFst_iff _).mp hα1
    rwa [coe_heckeAlphaBar] at this

  obtain ⟨dataN⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      jBar N ∈ u₀.toValuationSubring → b ∈ u₀.toValuationSubring :=
    Ws18Sep2V3MEMCK.mem_of_jBar_mem N dataN b hint

  obtain ⟨pN, hpN, hpNb⟩ :=
    ModularCurve.CharPModel.exists_monic_eval2_affineBaseFin_eq_zero_of_mem_modularLocalized_of_forall_mem_of_jBar_mem
      red hqN b hloc hreg
  have hbint : IsIntegral ↥(affineBaseFin N A) b := ⟨pN, hpN, hpNb⟩

  have hαint := Ws18Sep2V3MEMCK.isIntegral_heckeAlphaBar A N q hbint
  have hβint := Ws18Sep2V3MEMCK.isIntegral_heckeBetaBar A N q data hbint

  obtain ⟨Kα, fdα, hKα, hαmem⟩ :=
    ModularCurve.exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin A N _ hαint K
  obtain ⟨Kβ, fdβ, hKβ, hβmem⟩ :=
    ModularCurve.exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin A N _ hβint K
  haveI := fdα; haveI := fdβ
  refine ⟨Kα ⊔ Kβ, IntermediateField.finiteDimensional_sup Kα Kβ, le_trans hKα le_sup_left, fun K'' hfd hle => ?_⟩
  exact ⟨hαmem K'' hfd (le_trans le_sup_left hle), hβmem K'' hfd (le_trans le_sup_right hle)⟩

end Ws18Sep2V3
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

open Ws18Sep2V3 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (v : Place k (modularFunctionFieldC k N)) (hv : v ∈ ssPlaces q N k)
    (g : ↥(modularFunctionFieldBar (N * q)))
    (hg : ((g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.jIntegralClosure (N * q) A K))
    (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers) :
    (arithFrobC q k N • v).HasValue (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) ↔
      v.HasValue (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
  classical

  obtain ⟨K₀, hK₀fd, -, hgK₀⟩ := Ws18Sep2Alt.exists_subNF_mem_jIntegralClosure (N * q) A hg
  haveI := hK₀fd
  obtain ⟨K₂, hK₂fd, hK₀₂, hALg₂⟩ := exists_atkinLehnerBar_mem_jIntegralClosure hqN A red K₀ g hgK₀
  haveI := hK₂fd
  obtain ⟨K₁, hK₁fd, hK₁⟩ := exists_numberField_pow_sq_subset_range' (q := q) (A := A) (k := k) (red := red)
  haveI := hK₁fd
  let K' : IntermediateField ℚ (AlgebraicClosure ℚ) := K₂ ⊔ K₁
  haveI hK'fd : FiniteDimensional ℚ ↥K' := IntermediateField.finiteDimensional_sup K₂ K₁
  have hgK' : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K' :=
    Ws18Sep2Alt.jIntegralClosure_mono (N * q) A (hK₀₂.trans le_sup_left) hgK₀
  have hALgK' : ((atkinLehnerBar N q g : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      jIntegralClosure (N * q) A K' :=
    Ws18Sep2Alt.jIntegralClosure_mono (N * q) A le_sup_left hALg₂
  have hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (redRestrict red K') :=
    fun a ha => range_redRestrict_mono' (red := red) le_sup_right (hK₁ a ha)

  have hφv : arithFrobC q k N • v ∈ ssPlaces q N k := ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k v hv

  have hjv : ∀ K'' : IntermediateField ℚ (AlgebraicClosure ℚ), K' ≤ K'' →
      ∃ (a : k) (x : ↥(coeffSubring A K'')), v.evalAt (jGeomGen k N) = a ∧ redRestrict red K'' x = a := by
    intro K'' hle
    obtain ⟨x, hx⟩ := range_redRestrict_mono' (red := red) hle
      (hk₀ _ (ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hv.2.2))
    exact ⟨_, x, rfl, hx⟩
  have hjφv : ∀ K'' : IntermediateField ℚ (AlgebraicClosure ℚ), K' ≤ K'' →
      ∃ (a : k) (x : ↥(coeffSubring A K'')), (arithFrobC q k N • v).evalAt (jGeomGen k N) = a ∧
        redRestrict red K'' x = a := by
    intro K'' hle
    obtain ⟨x, hx⟩ := range_redRestrict_mono' (red := red) hle
      (hk₀ _ (ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hφv.2.2))
    exact ⟨_, x, rfl, hx⟩
  have hsub : ({jGeomGen k N} : Set ↥(modularFunctionFieldC k N)) ⊆ {jGeomGen k N, jNGeomGen k N} :=
    Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  constructor
  ·
    intro H2
    obtain ⟨h₀, hh₀⟩ := exists_coeffMap_eq_residue₂ R hqN K' v hv g hgK' h₂
    obtain ⟨h₂', hint₂⟩ :=
      (R.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure hqN K' g hgK').2.1
    have hint : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N)))
        (R.residue₂ ⟨g, h₂⟩ : ↥(modularFunctionFieldC k N)) :=
      isIntegral_of_subalgebra_le (Algebra.adjoin_mono hsub) hint₂
    obtain ⟨y, b, hby, hred, hbK, hintb⟩ :=
      ModularCurve.exists_fieldOver_lift_isIntegral_of_isIntegral red hqN K' h₀ (R.residue₂ ⟨g, h₂⟩) hh₀ hint
    obtain ⟨hβ₁, hβ₂, hresβ, hiffβ⟩ :=
      hasValue_residue_heckeBetaBar R hqN K' v hv y b (R.residue₂ ⟨g, h₂⟩) hby hred hbK hintb
    have hβv : v.HasValue (R.residue₁ ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, hβ₁⟩ : ↥(modularFunctionFieldC k N))
        (0 : k) := hiffβ.mpr H2
    obtain ⟨K₃, hK₃fd, hK'₃, hK₃⟩ := exists_forall_coe_heckeAlphaBar_mem_jIntegralClosure_and R hqN K' y b hby hbK hintb
    haveI := hK₃fd
    obtain ⟨-, hβC⟩ := hK₃ K₃ hK₃fd le_rfl

    have hr₂ : g - heckeBetaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers := sub_mem h₂ hβ₂
    have hrC : ((g - heckeBetaBar (AlgebraicClosure ℚ) N q b : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K₃ := by
      rw [AddSubgroupClass.coe_sub]
      exact sub_mem (Ws18Sep2Alt.jIntegralClosure_mono (N * q) A hK'₃ hgK') hβC
    have hres₂r : R.residue₂ ⟨g - heckeBetaBar (AlgebraicClosure ℚ) N q b, hr₂⟩ = 0 := by
      have e : (⟨g - heckeBetaBar (AlgebraicClosure ℚ) N q b, hr₂⟩ : ↥R.R₂.integers) =
          ⟨g, h₂⟩ - ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, hβ₂⟩ := rfl
      rw [e, map_sub, hresβ, sub_self]
    obtain ⟨a, x, ha, hx⟩ := hjv K₃ hK'₃
    obtain ⟨hr₁, hvr⟩ := R.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure hqN K₃ v hv a ha x hx
      (g - heckeBetaBar (AlgebraicClosure ℚ) N q b) hrC hr₂ hres₂r

    have e₁ : (⟨g, h₁⟩ : ↥R.R₁.integers) =
        ⟨g - heckeBetaBar (AlgebraicClosure ℚ) N q b, hr₁⟩ + ⟨heckeBetaBar (AlgebraicClosure ℚ) N q b, hβ₁⟩ :=
      Subtype.ext (sub_add_cancel g _).symm
    rw [e₁, map_add]
    have := hvr.add' hβv
    rwa [add_zero] at this
  ·
    intro H1
    obtain ⟨h₀, hh₀⟩ := exists_coeffMap_eq_residue₁ R hqN K' v hv g hgK' h₁
    obtain ⟨h₁', hint₁⟩ :=
      (R.exists_isIntegral_adjoin_residue_and_forall_exists_hasValue_of_mem_jIntegralClosure hqN K' g hgK').1
    have hint : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N)))
        (R.residue₁ ⟨g, h₁⟩ : ↥(modularFunctionFieldC k N)) :=
      isIntegral_of_subalgebra_le (Algebra.adjoin_mono hsub) hint₁
    obtain ⟨y, b, hby, hred, hbK, hintb⟩ :=
      ModularCurve.exists_fieldOver_lift_isIntegral_of_isIntegral red hqN K' h₀ (R.residue₁ ⟨g, h₁⟩) hh₀ hint
    obtain ⟨hα₁, hα₂, hresα, hiffα⟩ :=
      hasValue_residue_heckeAlphaBar R hqN K' v hv y b (R.residue₁ ⟨g, h₁⟩) hby hred hbK hintb
    have hαφv : (arithFrobC q k N • v).HasValue
        (R.residue₂ ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, hα₂⟩ : ↥(modularFunctionFieldC k N)) (0 : k) :=
      hiffα.mpr H1
    obtain ⟨K₃, hK₃fd, hK'₃, hK₃⟩ := exists_forall_coe_heckeAlphaBar_mem_jIntegralClosure_and R hqN K' y b hby hbK hintb
    haveI := hK₃fd
    obtain ⟨-, hβC⟩ := hK₃ K₃ hK₃fd le_rfl

    have hr₁ : g - heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₁.integers := sub_mem h₁ hα₁
    have hr₂ : g - heckeAlphaBar (AlgebraicClosure ℚ) N q b ∈ R.R₂.integers := sub_mem h₂ hα₂
    have hALr : atkinLehnerBar N q (g - heckeAlphaBar (AlgebraicClosure ℚ) N q b) =
        atkinLehnerBar N q g - heckeBetaBar (AlgebraicClosure ℚ) N q b := by
      rw [map_sub, (atkinLehnerBar_heckeAlphaBar' hqN b).1]
    have hALr₂ : atkinLehnerBar N q (g - heckeAlphaBar (AlgebraicClosure ℚ) N q b) ∈ R.R₂.integers := by
      rw [R.mem_integers₂_iff, atkinLehnerBar_atkinLehnerBar hqN]
      exact hr₁
    have hALrC : ((atkinLehnerBar N q (g - heckeAlphaBar (AlgebraicClosure ℚ) N q b) : ↥(modularFunctionFieldBar (N * q))) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K₃ := by
      rw [hALr, AddSubgroupClass.coe_sub]
      exact sub_mem (Ws18Sep2Alt.jIntegralClosure_mono (N * q) A hK'₃ hALgK') hβC
    have hres₁r : R.residue₁ ⟨g - heckeAlphaBar (AlgebraicClosure ℚ) N q b, hr₁⟩ = 0 := by
      have e : (⟨g - heckeAlphaBar (AlgebraicClosure ℚ) N q b, hr₁⟩ : ↥R.R₁.integers) =
          ⟨g, h₁⟩ - ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, hα₁⟩ := rfl
      rw [e, map_sub, hresα, sub_self]
    have hres₂ALr : R.residue₂ ⟨atkinLehnerBar N q (g - heckeAlphaBar (AlgebraicClosure ℚ) N q b), hALr₂⟩ = 0 := by
      rw [residue₂_apply, R.residue₂_eq,
        Ws18Sep2V3SERIES.residueFst_congr R _ hr₁ (atkinLehnerBar_atkinLehnerBar hqN _), ← residue₁_apply, hres₁r]
    obtain ⟨a, x, ha, hx⟩ := hjφv K₃ hK'₃
    obtain ⟨hALr₁, hw⟩ := R.hasValue_residueFst_zero_of_residueSnd_eq_zero_of_mem_jIntegralClosure hqN K₃
      (arithFrobC q k N • v) hφv a ha x hx (atkinLehnerBar N q (g - heckeAlphaBar (AlgebraicClosure ℚ) N q b))
      hALrC hALr₂ hres₂ALr
    rw [residue₁_atkinLehnerBar_eq_residue₂ R _ hr₂ hALr₁] at hw

    have e₂ : (⟨g, h₂⟩ : ↥R.R₂.integers) =
        ⟨g - heckeAlphaBar (AlgebraicClosure ℚ) N q b, hr₂⟩ + ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q b, hα₂⟩ :=
      Subtype.ext (sub_add_cancel g _).symm
    rw [e₂, map_add]
    have := hw.add' hαφv
    rwa [add_zero] at this

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure.Ws18Sep2Alt"

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_residueSnd_zero_iff_residueFst_of_mem_jIntegralClosure (solution)
