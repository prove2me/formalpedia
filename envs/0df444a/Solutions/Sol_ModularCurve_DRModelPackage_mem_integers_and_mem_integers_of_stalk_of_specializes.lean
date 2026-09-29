-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_integers_and_mem_integers_of_stalk_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/aee0cdaf-330f-5e67-9f8f-72d345597b18

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring
import Theorems.Thm_ModularCurve_DRModelPackage_isClosed_or_eq_generic_of_snd_eq_closedPoint
import Theorems.Thm_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersFst
import Theorems.Thm_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersSnd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_integers_and_mem_integers_of_stalk_of_specializes
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure"
p2m_attr_erase "instance" "continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

open Classical in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    :
    ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) ∈ R.R₁.integers ∧
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) ∈ R.R₂.integers := by

  haveI : IsProper (DRModel.toBase p) := 𝔛.isProper
  haveI hUC : UniversallyClosed (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := inferInstance

  have halg : ∀ t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x,
      algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t =
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes ((genericPoint_spec ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))).specializes trivial)).hom t :=
    fun _ => rfl
  have hconst : ∀ a : O,
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) =
      algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a))) := by
    intro a
    rw [halg]
    change _ = ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom _
    rw [TopCat.Presheaf.germ_stalkSpecializes]

  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ)⁻¹ ∉ A := by
    intro h
    have hpA' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
    have hmul : red ⟨_, hpA'⟩ * red ⟨_, h⟩ = 1 := by
      rw [← map_mul, ← map_one red]
      congr 1
      apply Subtype.ext
      simp [hp0]
    have hred : red ⟨_, hpA'⟩ = 0 := by
      have : (⟨((p : ℕ) : AlgebraicClosure ℚ), hpA'⟩ : A) = ((p : ℕ) : A) := Subtype.ext (by simp)
      rw [this, map_natCast, CharP.cast_eq_zero]
    rw [hred, zero_mul] at hmul
    exact zero_ne_one hmul

  have P1 : ∀ Rj : RegularProlongation A ↥(modularFunctionFieldBar (1 * p)) (modularFunctionFieldFullC (ResidueField A) 1),
      (∀ a : O, ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ Rj.integers.comap φ) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O, ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ (Rj.integers.comap φ).nonunits) := by
    intro Rj
    have hOV : ∀ a : O, ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (genericPoint ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) trivial).hom
        (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) ∈ Rj.integers.comap φ := by
      intro a
      rw [ValuationSubring.mem_comap, hconst, hφO a]
      exact (Rj.algebraMap_mem_iff _).mpr (hιA a)
    refine ⟨hOV, ?_⟩
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
    have hpV : ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) ∈ (Rj.integers.comap φ).nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_or]
      right
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
      intro h
      apply hpA
      rw [← Rj.algebraMap_mem_iff, map_inv₀, map_natCast]
      exact h
    obtain ⟨hp1, hp2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpV
    exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
      ⟨mul_mem hp1 (hOV c), Ideal.mul_mem_right ⟨_, hOV c⟩ _ hp2⟩

  obtain ⟨c₁, hc₁O, hdom₁, hmax₁⟩ :=
    AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      (R.R₁.integers.comap φ) (P1 R.R₁).1 (P1 R.R₁).2
  obtain ⟨c₂, hc₂O, hdom₂, hmax₂⟩ :=
    AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      (R.R₂.integers.comap φ) (P1 R.R₂).1 (P1 R.R₂).2
  have hdom₁' : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c₁,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.R₁.integers :=
    fun s => ValuationSubring.mem_comap.mp (hdom₁ s)
  have hdom₂' : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c₂,
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.R₂.integers :=
    fun s => ValuationSubring.mem_comap.mp (hdom₂ s)

  have hnu : ∀ (Rj : RegularProlongation A ↥(modularFunctionFieldBar (1 * p)) (modularFunctionFieldFullC (ResidueField A) 1))
      (t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField), t ∈ (Rj.integers.comap φ).nonunits → φ t ∈ Rj.integers.nonunits := by
    intro Rj t ht
    rw [ValuationSubring.mem_nonunits_iff_or] at ht ⊢
    rcases ht with ht | ht
    · left; rw [ht, map_zero]
    · right; rwa [ValuationSubring.mem_comap, map_inv₀] at ht
  have hmax₁' : ∀ s ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c₁),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.R₁.integers.nonunits :=
    fun s hs => hnu R.R₁ _ (hmax₁ s hs)
  have hmax₂' : ∀ s ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c₂),
      φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.R₂.integers.nonunits :=
    fun s hs => hnu R.R₂ _ (hmax₂ s hs)
  have hnc₁ := ModularCurve.DRModelPackage.not_isClosed_of_forall_stalk_mem_integersFst p hp 𝔛 O hϖ K ιK x φ hφO hφj
    P R hιA toκ htoκ c₁ hc₁O hdom₁' hmax₁'
  have hnc₂ := ModularCurve.DRModelPackage.not_isClosed_of_forall_stalk_mem_integersSnd p hp 𝔛 O hϖ K ιK x φ hφO hφj
    P R hιA toκ htoκ c₂ hc₂O hdom₂' hmax₂'
  have hgen₁ := (ModularCurve.DRModelPackage.isClosed_or_eq_generic_of_snd_eq_closedPoint p 𝔛 O hϖ k toκ c₁ hc₁O).resolve_left hnc₁
  have hgen₂ := (ModularCurve.DRModelPackage.isClosed_or_eq_generic_of_snd_eq_closedPoint p 𝔛 O hϖ k toκ c₂ hc₂O).resolve_left hnc₂

  have hspec : ∀ {η : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))} (h : η ⤳ x) (t : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
      algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t =
        algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk η) (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField
          (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes h).hom t) := by
    intro η h t
    change ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom t =
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes h ≫ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes _).hom t
    rw [TopCat.Presheaf.stalkSpecializes_comp]
  have key : ∀ (c : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (V : ValuationSubring (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField),
      (c = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ∨
        c = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) →
      (∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c, algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s ∈ V) →
      ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s ∈ V := by
    intro c V hc hdom s
    rcases hc with rfl | rfl
    · rw [hspec hsp₁]; exact hdom _
    · rw [hspec hsp₂]; exact hdom _
  intro s
  exact ⟨ValuationSubring.mem_comap.mp (key c₁ _ hgen₁ hdom₁ s),
    ValuationSubring.mem_comap.mp (key c₂ _ hgen₂ hdom₂ s)⟩

end S_ModularCurve_DRModelPackage_mem_integers_and_mem_integers_of_stalk_of_specializes
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_integers_and_mem_integers_of_stalk_of_specializes (solution)
