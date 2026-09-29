-- Prove2me | solution 1 for ModularCurve.XZeroP.exists_mem_ssPlaces_ringHom_eq_residueFst_of_mem_ssJSet_chartAlgFin_twoChartIntegralModel_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/95a669d6-46ca-5532-be1b-fbe7202e5639

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_XZeroP_le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_exists_mem_ssPlaces_ringHom_eq_residueFst_of_mem_ssJSet_chartAlgFin_twoChartIntegralModel_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instIsElliptic_tateBase TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix"
p2m_attr_erase "simp" "ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

namespace P2Help

section Generic
open ModularCurve

variable {L C : Type} [Field L] [CharZero L] [Field C] [CharZero C] (e : L →+* C)

theorem coeffMap_algebraMap (c : L) :
    coeffMap e (algebraMap L (LaurentSeries L) c) = algebraMap C (LaurentSeries C) (e c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap e (coeffEmb L x) = coeffEmb C x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) _

theorem coeffMap_mem_laurentBaseChange (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    {y : LaurentSeries L} (hy : y ∈ laurentBaseChange L F₀) :
    coeffMap e y ∈ laurentBaseChange C F₀ := by
  have hle : (laurentBaseChange L F₀).toSubfield.map (coeffMap e) ≤ (laurentBaseChange C F₀).toSubfield := by
    rw [laurentBaseChange, laurentBaseChange, IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield,
      RingHom.map_field_closure]
    apply Subfield.closure_mono
    rintro _ ⟨z, hz, rfl⟩
    rcases hz with ⟨c, rfl⟩ | ⟨x, hx, rfl⟩
    · exact Or.inl ⟨e c, (coeffMap_algebraMap e c).symm⟩
    · exact Or.inr ⟨x, hx, (coeffMap_coeffEmb e x).symm⟩
  exact hle ⟨y, hy, rfl⟩

theorem exists_ringHom_laurentBaseChange_coe_eq_coeffMap (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K₂ : IntermediateField L (LaurentSeries L)) (hK₂ : K₂ = laurentBaseChange L F₀) :
    ∃ ψ : ↥K₂ →+* ↥(laurentBaseChange C F₀),
      ∀ x : ↥K₂, ((ψ x : ↥(laurentBaseChange C F₀)) : LaurentSeries C) = coeffMap e ((x : ↥K₂) : LaurentSeries L) := by
  subst hK₂
  refine ⟨((coeffMap e).comp (laurentBaseChange L F₀).toSubfield.subtype).codRestrict
      (laurentBaseChange C F₀).toSubfield.toSubring (fun x => coeffMap_mem_laurentBaseChange e F₀ x.2), fun x => rfl⟩

end Generic

theorem exists_ringHom_modularFunctionFieldBar_coe_eq_coeffMap
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (e : L →+* AlgebraicClosure ℚ) :
    ∃ ψ : ↥K₂ →+* ↥(ModularCurve.modularFunctionFieldBar (M * p)),
      ∀ x : ↥K₂, ((ψ x : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ))
        = ModularCurve.coeffMap e ((x : ↥K₂) : LaurentSeries L) := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull] at hK₂
  exact exists_ringHom_laurentBaseChange_coe_eq_coeffMap e (ModularCurve.modularFunctionFieldFull (M * p)) K₂ hK₂

section GG
open ModularCurve AlgebraicCurve.TwoChartIntegralModel Polynomial

theorem exists_mem_chartAlgFin_coe_eq_coeffEmb_qExpand
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (L : Type) [Field L] [CharZero L]
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)] :
    ∃ jM : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₂) j₂),
      (((jM : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₂) j₂)) : ↥K₂) : LaurentSeries L)
        = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ M ModularCurve.jq) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩

  have hmem : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ M ModularCurve.jq) ∈ K₂ := by
    rw [hK₂, qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact coeffEmb_mem_laurentBaseChange L (jqd_mem_full (M * p) (dvd_mul_right M p))
  let jM : ↥K₂ := ⟨_, hmem⟩
  have hjM : ((jM : ↥K₂) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ M ModularCurve.jq) := rfl

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData M
  let B : Subalgebra A ↥K₂ := Algebra.adjoin A ({j₂} : Set ↥K₂)
  let jB : ↥B := ⟨j₂, Algebra.self_mem_adjoin_singleton A j₂⟩
  let ψ : Polynomial ℤ →+* ↥B := (Polynomial.aeval (R := ℤ) jB).toRingHom
  let P : Polynomial ↥B := data.Φ.map ψ
  have hPm : P.Monic := data.monic.map ψ

  have hcomp : (algebraMap ↥B ↥K₂).comp ψ = (Polynomial.aeval (R := ℤ) j₂).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · show algebraMap ↥B ↥K₂ (Polynomial.aeval (R := ℤ) jB Polynomial.X) = Polynomial.aeval (R := ℤ) j₂ Polynomial.X
      rw [Polynomial.aeval_X, Polynomial.aeval_X]; rfl

  have hcomp2 : ((K₂.val : ↥K₂ →+* LaurentSeries L)).comp (Polynomial.aeval (R := ℤ) j₂).toRingHom =
      (ModularCurve.coeffEmb L).comp evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro n; simp
    · show ((Polynomial.aeval (R := ℤ) j₂ Polynomial.X : ↥K₂) : LaurentSeries L) =
        ModularCurve.coeffEmb L (evalAtJ Polynomial.X)
      rw [Polynomial.aeval_X, evalAtJ_X, hj₂]
  have heval : Polynomial.eval₂ (algebraMap ↥B ↥K₂) jM P = 0 := by

    apply Subtype.val_injective
    show ((Polynomial.eval₂ (algebraMap ↥B ↥K₂) jM P : ↥K₂) : LaurentSeries L) = ((0 : ↥K₂) : LaurentSeries L)
    rw [ZeroMemClass.coe_zero]
    have h1 : Polynomial.eval₂ (algebraMap ↥B ↥K₂) jM P = Polynomial.eval₂ (Polynomial.aeval (R := ℤ) j₂).toRingHom jM data.Φ := by
      rw [Polynomial.eval₂_map, hcomp]
    rw [h1, show ((Polynomial.eval₂ (Polynomial.aeval (R := ℤ) j₂).toRingHom jM data.Φ : ↥K₂) : LaurentSeries L) =
        (K₂.val : ↥K₂ →+* LaurentSeries L) (Polynomial.eval₂ (Polynomial.aeval (R := ℤ) j₂).toRingHom jM data.Φ) from rfl,
      Polynomial.hom_eval₂, hcomp2]
    show Polynomial.eval₂ ((ModularCurve.coeffEmb L).comp evalAtJ) ((jM : ↥K₂) : LaurentSeries L) data.Φ = 0
    rw [hjM, show ModularCurve.qExpand ℚ M ModularCurve.jq = jqN M from rfl, ← Polynomial.hom_eval₂, data.eval_eq_zero, map_zero]
  have hint : IsIntegral ↥B jM := ⟨P, hPm, heval⟩
  exact ⟨⟨jM, (mem_chartAlg_iff A (↥K₂)).mpr hint⟩, rfl⟩

end GG

section FF
open ModularCurve IntermediateField AlgebraicCurve

section Transport

variable {κ E : Type*} [Field κ] [Field E] [Algebra κ E]

theorem finiteDimensional_adjoin_of_extendScalars (B : IntermediateField κ E) (a : ↥B)
    (h : IntermediateField.adjoin κ ({(a : E)} : Set E) ≤ B)
    [hfin : FiniteDimensional ↥(IntermediateField.adjoin κ ({(a : E)} : Set E)) ↥(extendScalars h)] :
    FiniteDimensional ↥(IntermediateField.adjoin κ ({a} : Set ↥B)) ↥B := by
  classical
  set A : IntermediateField κ E := IntermediateField.adjoin κ ({(a : E)} : Set E) with hAdef
  set A' : IntermediateField κ ↥B := IntermediateField.adjoin κ ({a} : Set ↥B) with hA'def
  have hlift : IntermediateField.lift A' = A := by
    rw [hA'def, IntermediateField.lift_adjoin, Set.image_singleton]

  have hmemA' : ∀ x : ↥A, (⟨(x : E), h x.2⟩ : ↥B) ∈ A' := by
    intro x
    have hx : (x : E) ∈ IntermediateField.lift A' := by rw [hlift]; exact x.2
    rw [IntermediateField.lift, IntermediateField.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : (⟨(x : E), h x.2⟩ : ↥B) = y := Subtype.ext hyx.symm
    rw [this]; exact hy

  let φ : ↥(extendScalars h) →+ ↥B :=
    { toFun := fun x => ⟨(x : E), (IntermediateField.mem_extendScalars h).mp x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφsmul : ∀ (c : ↥A) (x : ↥(extendScalars h)),
      φ (c • x) = (⟨⟨(c : E), h c.2⟩, hmemA' c⟩ : ↥A') • φ x := by
    intro c x
    apply Subtype.ext
    show ((c • x : ↥(extendScalars h)) : E) = (((⟨⟨(c : E), h c.2⟩, hmemA' c⟩ : ↥A') • φ x : ↥B) : E)
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin
  refine Module.finite_def.mpr ⟨s.image φ, ?_⟩
  rw [eq_top_iff]
  rintro b -
  have hb : (⟨(b : E), (IntermediateField.mem_extendScalars h).mpr b.2⟩ : ↥(extendScalars h)) ∈
      Submodule.span ↥A (s : Set ↥(extendScalars h)) := by rw [hs]; trivial
  have key : ∀ x : ↥(extendScalars h), x ∈ Submodule.span ↥A (s : Set ↥(extendScalars h)) →
      φ x ∈ Submodule.span ↥A' ((s.image φ : Finset ↥B) : Set ↥B) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact Set.mem_image_of_mem _ hy)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [hφsmul]; exact Submodule.smul_mem _ _ hy
  have := key _ hb
  have hφb : φ ⟨(b : E), (IntermediateField.mem_extendScalars h).mpr b.2⟩ = b := Subtype.ext rfl
  rwa [hφb] at this

end Transport

theorem finiteDimensional_adjoin_jGeomGen
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    FiniteDimensional ↥(IntermediateField.adjoin κ ({ModularCurve.jGeomGen κ M} : Set ↥(ModularCurve.modularFunctionFieldC κ M)))
      ↥(ModularCurve.modularFunctionFieldC κ M) := by
  have h : IntermediateField.adjoin κ ({((ModularCurve.jGeomGen κ M : ↥(ModularCurve.modularFunctionFieldC κ M)) : LaurentSeries κ)} :
      Set (LaurentSeries κ)) ≤ ModularCurve.modularFunctionFieldC κ M :=
    IntermediateField.adjoin_simple_le_iff.mpr (ModularCurve.jGeomGen κ M).2
  have hrel := ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi κ M p hpM
  have hfin : FiniteDimensional ↥(IntermediateField.adjoin κ ({((ModularCurve.jGeomGen κ M :
      ↥(ModularCurve.modularFunctionFieldC κ M)) : LaurentSeries κ)} : Set (LaurentSeries κ))) ↥(extendScalars h) := by
    apply FiniteDimensional.of_finrank_pos
    rw [← IntermediateField.relfinrank_eq_finrank_of_le h, ModularCurve.coe_jGeomGen, hrel]
    exact ModularCurve.dedekindPsi_pos M (NeZero.ne M)
  exact finiteDimensional_adjoin_of_extendScalars (ModularCurve.modularFunctionFieldC κ M) (ModularCurve.jGeomGen κ M) h

theorem transcendental_jGeomGen (κ : Type*) [Field κ] (M : ℕ) [NeZero M] :
    Transcendental κ (ModularCurve.jGeomGen κ M) := fun h =>
  (ModularCurve.transcendental_jqModC κ) (by
    rw [← ModularCurve.coe_jGeomGen κ M]
    exact IntermediateField.isAlgebraic_iff.mp h)

section RatFuncTower

variable {κ F : Type*} [Field κ] [Field F] [Algebra κ F]

theorem exists_ratFunc_algHom_finite (t : F) (ht : Transcendental κ t)
    [hfin : FiniteDimensional ↥(IntermediateField.adjoin κ ({t} : Set F)) F] :
    ∃ ψ : RatFunc κ →ₐ[κ] F, (∀ c : κ, ψ (algebraMap κ (RatFunc κ) c) = algebraMap κ F c) ∧
      (letI : Algebra (RatFunc κ) F := ψ.toRingHom.toAlgebra
       FiniteDimensional (RatFunc κ) F) := by
  classical
  let φ : Polynomial κ →ₐ[κ] F := Polynomial.aeval t
  have hφinj : Function.Injective φ := transcendental_iff_injective.mp ht
  have hφ : nonZeroDivisors (Polynomial κ) ≤ Submonoid.comap φ (nonZeroDivisors F) := by
    intro q hq
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    exact fun h0 => (mem_nonZeroDivisors_iff_ne_zero.mp hq) (hφinj (by rw [h0, map_zero]))
  let ψ : RatFunc κ →ₐ[κ] F := RatFunc.liftAlgHom φ hφ
  refine ⟨ψ, fun c => ψ.commutes c, ?_⟩
  letI algψ : Algebra (RatFunc κ) F := ψ.toRingHom.toAlgebra

  set T : IntermediateField κ F := IntermediateField.adjoin κ ({t} : Set F) with hTdef
  have hφmem : ∀ r : Polynomial κ, φ r ∈ T := fun r =>
    (IntermediateField.algebra_adjoin_le_adjoin κ ({t} : Set F)) (Polynomial.aeval_mem_adjoin_singleton κ t)
  have hψmem : ∀ f : RatFunc κ, ψ f ∈ T := by
    intro f
    induction f using RatFunc.induction_on with
    | f p q hq =>
      show RatFunc.liftAlgHom φ hφ _ ∈ T
      rw [RatFunc.liftAlgHom_apply_div]
      exact div_mem (hφmem p) (hφmem q)
  let ψT : RatFunc κ →+* ↥T := ψ.toRingHom.codRestrict T.toSubalgebra.toSubring hψmem
  have hψT : ∀ f, ((ψT f : ↥T) : F) = ψ f := fun _ => rfl
  have hψTsurj : Function.Surjective ψT := by
    intro x
    obtain ⟨r, s, hx⟩ := (IntermediateField.mem_adjoin_simple_iff κ (x : F)).mp x.2
    refine ⟨algebraMap _ _ r / algebraMap _ _ s, Subtype.ext ?_⟩
    rw [hψT, hx]
    exact RatFunc.liftAlgHom_apply_div φ hφ r s
  letI algT : Algebra (RatFunc κ) ↥T := ψT.toAlgebra
  haveI : IsScalarTower (RatFunc κ) ↥T F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (RatFunc κ) ↥T := Module.Finite.of_surjective (Algebra.linearMap (RatFunc κ) ↥T) hψTsurj
  exact Module.Finite.trans ↥T F

end RatFuncTower

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isRational_place_modularFunctionFieldC
    (κ : Type*) [Field κ] [IsAlgClosed κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (v : AlgebraicCurve.Place κ ↥(ModularCurve.modularFunctionFieldC κ M)) : v.IsRational := by
  haveI := finiteDimensional_adjoin_jGeomGen κ p M hpM
  obtain ⟨ψ, hψc, hfin⟩ := exists_ratFunc_algHom_finite (ModularCurve.jGeomGen κ M) (transcendental_jGeomGen κ M)
  letI : Algebra (RatFunc κ) ↥(ModularCurve.modularFunctionFieldC κ M) := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower κ (RatFunc κ) ↥(ModularCurve.modularFunctionFieldC κ M) :=
    IsScalarTower.of_algebraMap_eq fun c => (hψc c).symm
  haveI : FiniteDimensional (RatFunc κ) ↥(ModularCurve.modularFunctionFieldC κ M) := hfin
  exact AlgebraicCurve.Place.isRational_of_isAlgClosed v

end FF

theorem mem_of_isIntegral_of_forall_algebraMap_mem {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (W : ValuationSubring K) (hR : ∀ r : R, algebraMap R K r ∈ W) {x : K} (hx : IsIntegral R x) : x ∈ W := by
  let φ : R →+* ↥W := (algebraMap R K).codRestrict W hR
  have hx' : IsIntegral ↥W x := hx.map_of_comp_eq φ (RingHom.id K) (by ext r; rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx'
  rw [← hy]; exact y.2

theorem mem_nonunits_iff' {F : Type*} [Field F] (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff]
  by_cases hx : x = 0
  · subst hx
    simp [A.zero_mem]
  · constructor
    · intro h
      refine ⟨(A.valuation_le_one_iff x).mp h.le, Or.inr ?_⟩
      intro hinv
      have h1 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀] at h1
      have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
      have : 1 ≤ A.valuation x := by
        rwa [inv_le_one₀ (zero_lt_iff.mpr hx')] at h1
      exact absurd h (not_lt.mpr this)
    · rintro ⟨-, h0 | hinv⟩
      · exact absurd h0 hx
      · by_contra hlt
        apply hinv
        rw [← A.valuation_le_one_iff, map_inv₀]
        have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
        rw [inv_le_one₀ (zero_lt_iff.mpr hx')]
        exact not_lt.mp hlt

theorem exists_pow_eq_self_of_isAlgebraic {F κ : Type*} [Field F] [Fintype F] [Field κ] [Algebra F κ]
    {c : κ} (hc : IsAlgebraic F c) : ∃ N : ℕ, 2 ≤ N ∧ c ^ N = c := by
  haveI := IntermediateField.adjoin.finiteDimensional hc.isIntegral
  haveI : Finite ↥(IntermediateField.adjoin F ({c} : Set κ)) := Module.finite_of_finite F
  letI := Fintype.ofFinite ↥(IntermediateField.adjoin F ({c} : Set κ))
  refine ⟨Fintype.card ↥(IntermediateField.adjoin F ({c} : Set κ)), Fintype.one_lt_card, ?_⟩
  have h := FiniteField.pow_card
    (⟨c, IntermediateField.mem_adjoin_simple_self F c⟩ : ↥(IntermediateField.adjoin F ({c} : Set κ)))
  have h' := congrArg Subtype.val h
  simpa using h'

theorem mem_of_pow_eq_self {F : Type*} [Field F] (P : ValuationSubring F) {x : F} {N : ℕ} (hN : 2 ≤ N)
    (hx : x ^ N = x) : x ∈ P := by
  by_cases hx0 : x = 0
  · rw [hx0]; exact P.zero_mem
  rw [← P.valuation_le_one_iff]
  by_contra hlt
  push Not at hlt
  have h1 : P.valuation x ^ N = P.valuation x := by rw [← map_pow, hx]
  have h2 : 1 < P.valuation x ^ (N - 1) := one_lt_pow₀ hlt (by omega)
  have h3 : P.valuation x ^ N = P.valuation x ^ (N - 1) * P.valuation x := by
    rw [← pow_succ]; congr 1; omega
  rw [h3] at h1
  have hv0 : P.valuation x ≠ 0 := (map_ne_zero _).mpr hx0
  have : P.valuation x ^ (N - 1) = 1 := by
    have := mul_right_cancel₀ hv0 (h1.trans (one_mul _).symm)
    exact this
  exact (lt_irrefl _) (this ▸ h2)

theorem exists_valuationSubring_mem_and_mem_nonunits_iff
    {B F : Type*} [CommRing B] [Field F] (ρ : B →+* F) (y : Ideal B) [y.IsPrime]
    (hker : RingHom.ker ρ ≤ y) :
    ∃ P : ValuationSubring F, (∀ b, ρ b ∈ P) ∧ (∀ b, ρ b ∈ P.nonunits ↔ b ∈ y) := by
  classical
  let A : Subring F := ρ.range
  let ρ' : B →+* ↥A := ρ.rangeRestrict
  have hρ' : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hkerρ' : RingHom.ker ρ' = RingHom.ker ρ := RingHom.ker_rangeRestrict ρ
  let 𝔫 : Ideal ↥A := y.map ρ'
  haveI h𝔫 : 𝔫.IsPrime := Ideal.map_isPrime_of_surjective hρ' (by rw [hkerρ']; exact hker)
  have hcomap : 𝔫.comap ρ' = y := by
    rw [Ideal.comap_map_of_surjective _ hρ', sup_eq_left]
    intro b hb
    have hb' : b ∈ RingHom.ker ρ' := by
      rw [RingHom.mem_ker]; exact Ideal.mem_bot.mp (Ideal.mem_comap.mp hb)
    exact hker (hkerρ' ▸ hb')
  have hmem𝔫 : ∀ b : B, ρ' b ∈ 𝔫 ↔ b ∈ y := fun b => by rw [← Ideal.mem_comap, hcomap]
  let R : LocalSubring F := LocalSubring.ofPrime A 𝔫
  obtain ⟨P, hP⟩ := R.exists_le_valuationSubring
  obtain ⟨hRP, hloc⟩ := LocalSubring.le_def.mp hP
  have hAR : A ≤ R.toSubring := LocalSubring.le_ofPrime A 𝔫
  have hρP : ∀ b : B, ρ b ∈ P := fun b => hRP (hAR ⟨b, rfl⟩)
  refine ⟨P, hρP, fun b => ?_⟩
  haveI : IsLocalization.AtPrime ↥R.toSubring 𝔫 := by
    show IsLocalization.AtPrime ↥(LocalSubring.ofPrime A 𝔫).toSubring 𝔫
    infer_instance
  let r : ↥R.toSubring := algebraMap ↥A ↥R.toSubring (ρ' b)
  let ι : ↥R.toSubring →+* ↥P :=
    { toFun := fun x => ⟨(x : F), hRP x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιloc : ∀ x : ↥R.toSubring, IsUnit (ι x) → IsUnit x := fun x hx => by
    apply hloc.map_nonunit
    obtain ⟨u, hu⟩ := hx
    refine ⟨⟨⟨(u : ↥P).1, (u : ↥P).2⟩, ⟨(↑u⁻¹ : ↥P).1, (↑u⁻¹ : ↥P).2⟩, ?_, ?_⟩, ?_⟩
    · exact Subtype.ext (congrArg Subtype.val u.mul_inv)
    · exact Subtype.ext (congrArg Subtype.val u.inv_mul)
    · exact Subtype.ext (congrArg Subtype.val hu)
  have h1 : b ∈ y ↔ r ∈ IsLocalRing.maximalIdeal ↥R.toSubring := by
    rw [← hmem𝔫, ← IsLocalization.AtPrime.to_map_mem_maximal_iff ↥R.toSubring 𝔫 (ρ' b)]
  rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hb, hmax⟩ hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
    exact hmax (by first | exact hu.map ι | simpa [ι] using (hu.map ι))
  · intro hnu
    refine ⟨hρP b, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hnu (hιloc r (by first | exact hu | simpa [ι] using hu))

end P2Help

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)

    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (y₂ : ↥(XFin A (↥K₂) j₂))
    (hss₂ : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₂) j₂) →+* Ω),
      RingHom.ker φ = y₂.asIdeal → φ (jChartFin A (↥K₂) j₂) ∈ ModularCurve.ssJSet p Ω)
    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂)) (h𝔶₂ : 𝔶₂ = y₂.asIdeal)
    (h𝔶₂ϖ : algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ ∈ 𝔶₂)

    (e : L →+* AlgebraicClosure ℚ)
    (Ab : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥Ab) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Ab)]
    [DecidableEq (IsLocalRing.ResidueField ↥Ab)]
    (hA : ∀ a : A, e (algebraMap A L a) ∈ Ab)
    (hAm : ∀ a : A, (⟨e (algebraMap A L a), hA a⟩ : ↥Ab) ∈ IsLocalRing.maximalIdeal ↥Ab ↔ a ∈ IsLocalRing.maximalIdeal A)

    (data : ModularCurve.ModularPolynomialData p) (hKr : ModularCurve.KroneckerCongruence p data)
    (hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M p)
    (hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) M p)
    (P : ModularCurve.PlaceSpecialization Ab p M data hKr (IsLocalRing.ResidueField ↥Ab) (IsLocalRing.residue ↥Ab) hα hβ)
    (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) :
    ∃ (w : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Ab) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M))
      (_ : w ∈ ModularCurve.ssPlaces p M (IsLocalRing.ResidueField ↥Ab))
      (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)),

      (∀ b : ↥(chartAlgFin A (↥K₂) j₂), ∃ (f : ↥(ModularCurve.modularFunctionFieldBar (M * p))) (hf : f ∈ R.R₁.integers),
        ((f : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L) ∧
          ρ b = R.residue₁ ⟨f, hf⟩) ∧

      ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0 ∧
      ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M ∧
      (∀ b, ρ b ∈ w.toValuationSubring) ∧
      (∀ b, ρ b ∈ w.toValuationSubring.nonunits ↔ b ∈ 𝔶₂) ∧
      (∀ f : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M),
        ∃ a b : ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥Ab) (Set.range ρ)),
          (b : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)) ≠ 0 ∧ f * b = a) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ψ, hψ⟩ := P2Help.exists_ringHom_modularFunctionFieldBar_coe_eq_coeffMap p M L K₂ hK₂ e
  have hψA : ∀ a : A, ψ (algebraMap A ↥K₂ a)
      = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar (M * p)) (e (algebraMap A L a)) := by
    intro a
    apply Subtype.ext
    rw [hψ, IsScalarTower.algebraMap_apply A L ↥K₂ a]
    exact P2Help.coeffMap_algebraMap e _
  have hR1A : ∀ a : A, ψ (algebraMap A ↥K₂ a) ∈ R.R₁.integers := fun a => by
    rw [hψA]; exact (R.R₁.algebraMap_mem_iff _).mpr (hA a)
  have hψj : ((ψ j₂ : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ))
      = ModularCurve.jqModC (AlgebraicClosure ℚ) := by
    rw [hψ, hj₂, P2Help.coeffMap_coeffEmb, ModularCurve.coeffEmb]
    exact ModularCurve.coeffSemilinearAut.coeffMap_jqModC _
  have hjbar : ModularCurve.coeffMap Ab.subtype (ModularCurve.jqModC ↥Ab)
      = ((ψ j₂ : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hψj]; exact ModularCurve.coeffSemilinearAut.coeffMap_jqModC _
  obtain ⟨hR1j, hresj⟩ := R.residue₁_coeffMap (ModularCurve.jqModC ↥Ab)
    (by rw [hjbar]; exact (ψ j₂).2)
  have hjel : (⟨ModularCurve.coeffMap Ab.subtype (ModularCurve.jqModC ↥Ab), by rw [hjbar]; exact (ψ j₂).2⟩
      : ↥(ModularCurve.modularFunctionFieldBar (M * p))) = ψ j₂ := Subtype.ext hjbar
  have hR1j' : ψ j₂ ∈ R.R₁.integers := hjel ▸ hR1j
  have hadj : ∀ x ∈ Algebra.adjoin A ({j₂} : Set ↥K₂), ψ x ∈ R.R₁.integers := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff] at hx; subst hx; exact hR1j'
    | algebraMap a => exact hR1A a
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hR1 : ∀ b : ↥(chartAlgFin A (↥K₂) j₂), ψ (b : ↥K₂) ∈ R.R₁.integers := by
    intro b
    have hb : IsIntegral ↥(Algebra.adjoin A ({j₂} : Set ↥K₂)) (b : ↥K₂) :=
      (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K₂)).mp b.2
    let φ : ↥(Algebra.adjoin A ({j₂} : Set ↥K₂)) →+* ↥R.R₁.integers :=
      (ψ.comp (Algebra.adjoin A ({j₂} : Set ↥K₂)).val.toRingHom).codRestrict R.R₁.integers (fun s => hadj s s.2)
    have hb' : IsIntegral ↥R.R₁.integers (ψ (b : ↥K₂)) := hb.map_of_comp_eq φ ψ (by ext s; rfl)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hb'
    rw [← hy]; exact y.2

  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥(chartAlgFin A (↥K₂) j₂) →+*
      ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M),
      ∀ b, ρ b = R.residue₁ ⟨ψ (b : ↥K₂), hR1 b⟩ :=
    ⟨R.residue₁.comp ((ψ.comp (chartAlgFin A (↥K₂) j₂).val.toRingHom).codRestrict R.R₁.integers hR1),
      fun b => rfl⟩

  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hρA : ∀ a : A, ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) a)
      = R.ι (algebraMap (IsLocalRing.ResidueField ↥Ab)
          ↥(ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField ↥Ab) M)
          (IsLocalRing.residue ↥Ab ⟨e (algebraMap A L a), hA a⟩)) := by
    intro a
    rw [hρ, ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply]
    congr 1
    rw [← R.R₁.residue_algebraMap ⟨e (algebraMap A L a), hA a⟩]
    congr 1
    apply Subtype.ext
    show ψ ((algebraMap A ↥(chartAlgFin A (↥K₂) j₂) a : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) = _
    rw [Subalgebra.coe_algebraMap]
    exact hψA a
  have hρϖ : ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0 := by
    rw [hρA]
    have h0 : IsLocalRing.residue ↥Ab ⟨e (algebraMap A L ϖ), hA ϖ⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr ((hAm ϖ).mpr hϖm)
    rw [h0, map_zero, map_zero]

  have hρj : ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M := by
    apply Subtype.ext
    rw [ModularCurve.coe_jGeomGen, hρ, ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply, R.ι_coe]
    have hel : (⟨ψ ((jChartFin A (↥K₂) j₂ : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂), hR1 _⟩ : ↥R.R₁.integers)
        = ⟨_, hR1j⟩ := Subtype.ext hjel.symm
    rw [hel, hresj, ModularCurve.coeffSemilinearAut.coeffMap_jqModC, ModularCurve.coeffSemilinearAut.coeffMap_jqModC]

  obtain ⟨jM, hjM⟩ := P2Help.exists_mem_chartAlgFin_coe_eq_coeffEmb_qExpand p M L K₂ hK₂ A j₂ hj₂
  have hψjM : ((ψ (jM : ↥K₂) : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ))
      = ModularCurve.jqNModC (AlgebraicClosure ℚ) M := by
    rw [hψ, hjM, P2Help.coeffMap_coeffEmb, ModularCurve.coeffEmb, ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
    show ModularCurve.qExpand (AlgebraicClosure ℚ) M (ModularCurve.coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (ModularCurve.jqModC ℚ)) = _
    rw [ModularCurve.coeffSemilinearAut.coeffMap_jqModC]; rfl
  have hjMbar : ModularCurve.coeffMap Ab.subtype (ModularCurve.jqNModC ↥Ab M)
      = ((ψ (jM : ↥K₂) : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hψjM]; exact ModularCurve.coeffSemilinearAut.coeffMap_jqNModC _ M
  obtain ⟨hR1jM, hresjM⟩ := R.residue₁_coeffMap (ModularCurve.jqNModC ↥Ab M) (by rw [hjMbar]; exact (ψ _).2)
  have hρjM : ρ jM = ModularCurve.jNGeomGen (IsLocalRing.ResidueField ↥Ab) M := by
    apply Subtype.ext
    rw [ModularCurve.coe_jNGeomGen, hρ, ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply, R.ι_coe]
    have hel : (⟨ψ ((jM : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂), hR1 _⟩ : ↥R.R₁.integers) = ⟨_, hR1jM⟩ :=
      Subtype.ext (Subtype.ext hjMbar.symm)
    rw [hel, hresjM, ModularCurve.coeffSemilinearAut.coeffMap_jqNModC, ModularCurve.coeffSemilinearAut.coeffMap_jqNModC]

  haveI h𝔶₂p : 𝔶₂.IsPrime := h𝔶₂ ▸ y₂.isPrime

  let rA : A →+* IsLocalRing.ResidueField ↥Ab :=
    (IsLocalRing.residue ↥Ab).comp ((e.comp (algebraMap A L)).codRestrict Ab (fun a => hA a))
  have hrA : ∀ a, rA a = IsLocalRing.residue ↥Ab ⟨e (algebraMap A L a), hA a⟩ := fun a => rfl
  have hιalg : ∀ c : IsLocalRing.ResidueField ↥Ab,
      R.ι (algebraMap (IsLocalRing.ResidueField ↥Ab)
        ↥(ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField ↥Ab) M) c)
        = algebraMap (IsLocalRing.ResidueField ↥Ab)
          ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    apply Subtype.ext
    rw [R.ι_coe]
    show ModularCurve.coeffMap R.redBar (algebraMap (IsLocalRing.ResidueField ↥Ab) (LaurentSeries (IsLocalRing.ResidueField ↥Ab))
        (IsLocalRing.residue ↥Ab a)) = algebraMap _ (LaurentSeries _) (IsLocalRing.residue ↥Ab a)
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single, R.redBar_residue]
  have hρA' : ∀ a : A, ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) a)
      = algebraMap (IsLocalRing.ResidueField ↥Ab) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M) (rA a) :=
    fun a => by rw [hρA, hιalg]; rfl

  have htg : ∀ P : Polynomial (IsLocalRing.ResidueField ↥Ab),
      Polynomial.aeval (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) P = 0 → P = 0 := by
    intro P hP
    apply transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField ↥Ab))
    have key : (Polynomial.aeval (ModularCurve.jqModC (IsLocalRing.ResidueField ↥Ab))) P
        = ((Polynomial.aeval (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) P :
            ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)) : LaurentSeries (IsLocalRing.ResidueField ↥Ab)) := by
      rw [← ModularCurve.coe_jGeomGen (IsLocalRing.ResidueField ↥Ab) M]
      exact Polynomial.aeval_algHom_apply (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M).val
        (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) P
    rw [map_zero, key, hP]
    rfl

  have htj : Transcendental A j₂ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₂ A j₂ hj₂
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * p) := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 (M * p)) hT L K₂ hK₂ j₂ hj₂
  haveI := hFD
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ := inferInstance
  letI algP : Algebra (Polynomial A) ↥(chartAlgFin A (↥K₂) j₂) := (polynomialToChartFin A (↥K₂) j₂).toRingHom.toAlgebra
  have hφ : ∀ P : Polynomial A, algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₂) j₂) P = polynomialToChartFin A (↥K₂) j₂ P :=
    fun _ => rfl
  haveI hfin : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K₂) j₂) :=
    (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K₂) j₂ htj hFD hsep).1
  haveI hintP : Algebra.IsIntegral (Polynomial A) ↥(chartAlgFin A (↥K₂) j₂) := Algebra.IsIntegral.of_finite _ _

  have heval : ∀ P : Polynomial A, ρ (polynomialToChartFin A (↥K₂) j₂ P)
      = Polynomial.aeval (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) (P.map rA) := by
    intro P
    show ρ (Polynomial.aeval (jChartFin A (↥K₂) j₂) P) = _
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map, hρj]
    congr 1
    exact RingHom.ext fun a => hρA' a
  have hdiv : ∀ P : Polynomial A, ρ (polynomialToChartFin A (↥K₂) j₂ P) = 0 → Polynomial.C ϖ ∣ P := by
    intro P hP
    rw [heval] at hP
    have hmap : P.map rA = 0 := htg _ hP
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hi : rA (P.coeff i) = 0 := by
      have := congrArg (fun Q : Polynomial (IsLocalRing.ResidueField ↥Ab) => Q.coeff i) hmap
      simpa [Polynomial.coeff_map] using this
    rw [hrA, IsLocalRing.residue_eq_zero_iff, hAm, hϖ, Ideal.mem_span_singleton] at hi
    exact hi

  set 𝔭₀ : Ideal ↥(chartAlgFin A (↥K₂) j₂) := RingHom.ker ρ with h𝔭₀def
  haveI h𝔭₀p : 𝔭₀.IsPrime := RingHom.ker_isPrime ρ
  set ϖB : ↥(chartAlgFin A (↥K₂) j₂) := algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ with hϖBdef
  have hϖB𝔭 : ϖB ∈ 𝔭₀ := by rw [h𝔭₀def, RingHom.mem_ker]; exact hρϖ
  have hϖB0 : ϖB ≠ 0 := by
    intro h
    have h1 : ϖ = 0 := by
      have h2 : algebraMap A ↥K₂ ϖ = 0 := by
        have : ((ϖB : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) = 0 := by rw [h]; rfl
        rwa [hϖBdef, Subalgebra.coe_algebraMap] at this
      rw [IsScalarTower.algebraMap_apply A L ↥K₂] at h2
      have h3 : algebraMap A L ϖ = 0 := (map_eq_zero_iff (algebraMap L ↥K₂) (algebraMap L ↥K₂).injective).mp h2
      exact (map_eq_zero_iff (algebraMap A L) (IsFractionRing.injective A L)).mp h3
    have : IsLocalRing.maximalIdeal A = ⊥ := by rw [hϖ, h1, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_a_field A this
  have hcontr : ∀ P : Polynomial A, algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₂) j₂) P ∈ 𝔭₀ →
      ∃ P' : Polynomial A, P = Polynomial.C ϖ * P' := by
    intro P hP
    rw [hφ, h𝔭₀def, RingHom.mem_ker] at hP
    exact hdiv P hP
  have hmin : 𝔭₀ ∈ (Ideal.span ({ϖB} : Set ↥(chartAlgFin A (↥K₂) j₂))).minimalPrimes := by
    refine ⟨⟨h𝔭₀p, (Ideal.span_singleton_le_iff_mem _).mpr hϖB𝔭⟩, ?_⟩
    rintro Q ⟨hQp, hQle⟩ hQ𝔭₀
    by_contra hnot
    obtain ⟨s, hs𝔭, hsQ⟩ := Set.not_subset.mp hnot
    haveI := hQp
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := Polynomial A) hQ𝔭₀ ⟨hs𝔭, hsQ⟩
      (Algebra.IsIntegral.isIntegral s)
    apply hlt.ne
    apply le_antisymm (Ideal.comap_mono hQ𝔭₀)
    intro P hP
    rw [Ideal.mem_comap] at hP ⊢
    obtain ⟨P', rfl⟩ := hcontr P hP
    rw [map_mul]
    apply Q.mul_mem_right
    have : algebraMap (Polynomial A) ↥(chartAlgFin A (↥K₂) j₂) (Polynomial.C ϖ) = ϖB := by
      rw [hφ, hϖBdef, Polynomial.C_eq_algebraMap, AlgHom.commutes]
    rw [this]
    exact hQle (Ideal.mem_span_singleton_self ϖB)

  have hker : RingHom.ker ρ ≤ 𝔶₂ :=
    ModularCurve.XZeroP.le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ 𝔶₂ h𝔶₂ϖ
      (fun Ω _ _ _ _ φ hφ => hss₂ Ω φ (hφ.trans h𝔶₂)) 𝔭₀ hmin

  have hstrict : ∃ s : ↥(chartAlgFin A (↥K₂) j₂), s ∈ 𝔶₂ ∧ ρ s ≠ 0 := by
    haveI : IsDomain (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂) := Ideal.Quotient.isDomain 𝔶₂
    let Ω := AlgebraicClosure (FractionRing (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂))
    letI : DecidableEq Ω := Classical.decEq Ω
    let φ₀ : ↥(chartAlgFin A (↥K₂) j₂) →+* Ω :=
      (algebraMap (FractionRing (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂)) Ω).comp
        ((algebraMap (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂) (FractionRing (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂))).comp
          (Ideal.Quotient.mk 𝔶₂))
    have hφ₀ker : RingHom.ker φ₀ = 𝔶₂ := by
      ext b
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.comp_apply,
        map_eq_zero_iff _ (algebraMap (FractionRing (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂)) Ω).injective,
        map_eq_zero_iff _ (IsFractionRing.injective (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂)
          (FractionRing (↥(chartAlgFin A (↥K₂) j₂) ⧸ 𝔶₂))),
        Ideal.Quotient.eq_zero_iff_mem]
    have hpϖ : ((p : ℕ) : ↥(chartAlgFin A (↥K₂) j₂)) ∈ 𝔶₂ := by
      have hpA : (p : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAp
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hpA
      rw [← map_natCast (algebraMap A ↥(chartAlgFin A (↥K₂) j₂)), ← ht, map_mul]
      exact 𝔶₂.mul_mem_left _ h𝔶₂ϖ
    haveI : CharP Ω p := by
      have h0 : ((p : ℕ) : Ω) = 0 := by
        rw [← map_natCast φ₀, ← RingHom.mem_ker, hφ₀ker]; exact hpϖ
      exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0)
    have hssΩ := hss₂ Ω φ₀ (hφ₀ker.trans h𝔶₂)
    have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet p hssΩ
    refine ⟨jChartFin A (↥K₂) j₂ ^ (p ^ 2) - jChartFin A (↥K₂) j₂, ?_, ?_⟩
    · rw [← hφ₀ker, RingHom.mem_ker, map_sub, map_pow, hpow, sub_self]
    · rw [map_sub, map_pow, hρj]
      intro h
      have hP : Polynomial.aeval (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M)
          (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial (IsLocalRing.ResidueField ↥Ab)) = 0 := by
        rw [map_sub, map_pow, Polynomial.aeval_X]; exact h
      exact FiniteField.X_pow_card_sub_X_ne_zero (IsLocalRing.ResidueField ↥Ab)
        (Nat.one_lt_pow (by norm_num) hp.one_lt) (htg _ hP)

  obtain ⟨P₀, hP₀, hP₀y⟩ := P2Help.exists_valuationSubring_mem_and_mem_nonunits_iff ρ 𝔶₂ hker
  have hκP₀ : ∀ c : IsLocalRing.ResidueField ↥Ab,
      algebraMap (IsLocalRing.ResidueField ↥Ab) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M) c ∈ P₀ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥Ab) := ZMod.algebra _ p
    have halg : IsAlgebraic (ZMod p) (IsLocalRing.residue ↥Ab a) := ValuationSubring.isAlgebraic_residue Ab hp a
    obtain ⟨N, hN, hcN⟩ := P2Help.exists_pow_eq_self_of_isAlgebraic halg
    exact P2Help.mem_of_pow_eq_self P₀ hN (by rw [← map_pow, hcN])
  have hP₀top : P₀ ≠ ⊤ := by
    obtain ⟨s, hs, hs0⟩ := hstrict
    intro htop
    have hsn : ρ s ∈ P₀.nonunits := (hP₀y s).mpr hs
    rw [P2Help.mem_nonunits_iff'] at hsn
    rcases hsn.2 with h | h
    · exact hs0 h
    · exact h (htop ▸ ValuationSubring.mem_top _)
  haveI := P2Help.finiteDimensional_adjoin_jGeomGen (IsLocalRing.ResidueField ↥Ab) p M hpM
  have hPIR : IsPrincipalIdealRing ↥P₀ :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin
      (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) P₀ hκP₀ hP₀top
  obtain ⟨w, hw⟩ : ∃ w : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Ab)
      ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M), w.toValuationSubring = P₀ :=
    ⟨⟨P₀, hκP₀, hP₀top, hPIR⟩, rfl⟩
  subst hw

  have hrat : w.IsRational := P2Help.isRational_place_modularFunctionFieldC _ p M hpM w
  have hss : w ∈ ModularCurve.ssPlaces p M (IsLocalRing.ResidueField ↥Ab) := by
    refine ⟨hrat, ⟨?_, ?_⟩, ?_⟩
    · show ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M ∈ w.toValuationSubring
      rw [← hρj]; exact hP₀ _
    · show ModularCurve.jNGeomGen (IsLocalRing.ResidueField ↥Ab) M ∈ w.toValuationSubring
      rw [← hρjM]; exact hP₀ _
    ·
      let eqv : IsLocalRing.ResidueField ↥Ab ≃+* w.ResidueField :=
        RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField ↥Ab) w.ResidueField)
          ⟨(algebraMap (IsLocalRing.ResidueField ↥Ab) w.ResidueField).injective, hrat⟩
      let ρP : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥w.toValuationSubring := ρ.codRestrict w.toValuationSubring hP₀
      let φ₁ : ↥(chartAlgFin A (↥K₂) j₂) →+* IsLocalRing.ResidueField ↥Ab :=
        eqv.symm.toRingHom.comp ((IsLocalRing.residue ↥w.toValuationSubring).comp ρP)
      have hφ₁ : ∀ b, algebraMap (IsLocalRing.ResidueField ↥Ab) w.ResidueField (φ₁ b)
          = IsLocalRing.residue ↥w.toValuationSubring (ρP b) := fun b => eqv.apply_symm_apply _
      have hφ₁ker : RingHom.ker φ₁ = 𝔶₂ := by
        ext b
        rw [RingHom.mem_ker, ← hP₀y, ← map_eq_zero_iff _ (algebraMap (IsLocalRing.ResidueField ↥Ab) w.ResidueField).injective,
          hφ₁, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
        rfl
      have hssκ := hss₂ (IsLocalRing.ResidueField ↥Ab) φ₁ (hφ₁ker.trans h𝔶₂)
      have hjP : ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M ∈ w.toValuationSubring := by
        rw [← hρj]; exact hP₀ _
      have hev : w.evalAt (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) = φ₁ (jChartFin A (↥K₂) j₂) := by
        apply (algebraMap (IsLocalRing.ResidueField ↥Ab) w.ResidueField).injective
        rw [w.algebraMap_evalAt hrat hjP, hφ₁]
        congr 1
        apply Subtype.ext
        show ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M = ρ (jChartFin A (↥K₂) j₂)
        rw [hρj]
      show w.evalAt (ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M) ∈ ModularCurve.ssJSet p (IsLocalRing.ResidueField ↥Ab)
      rw [hev]; exact hssκ

  have hbir : ∀ f : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M),
      ∃ a b : ↥(Algebra.adjoin (IsLocalRing.ResidueField ↥Ab) (Set.range ρ)),
        (b : ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)) ≠ 0 ∧ f * b = a := by
    intro f

    have hf : f ∈ IntermediateField.adjoin (IsLocalRing.ResidueField ↥Ab)
        ({ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M, ModularCurve.jNGeomGen (IsLocalRing.ResidueField ↥Ab) M} :
          Set ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)) := by
      have hmap := IntermediateField.adjoin_map (IsLocalRing.ResidueField ↥Ab)
        ({ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M, ModularCurve.jNGeomGen (IsLocalRing.ResidueField ↥Ab) M} :
          Set ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M))
        (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M).val
      have hfv : (f : LaurentSeries (IsLocalRing.ResidueField ↥Ab)) ∈ IntermediateField.adjoin (IsLocalRing.ResidueField ↥Ab)
          ((ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M).val ''
            ({ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M, ModularCurve.jNGeomGen (IsLocalRing.ResidueField ↥Ab) M} :
              Set ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M))) := by
        rw [Set.image_pair]
        exact f.2
      rw [← hmap, IntermediateField.mem_map] at hfv
      obtain ⟨y, hy, hyx⟩ := hfv
      have hfy : f = y := Subtype.ext hyx.symm
      rw [hfy]; exact hy
    rw [IntermediateField.mem_adjoin_iff_div] at hf
    obtain ⟨r, hr, s, hs, hfrs⟩ := hf
    have hle : Algebra.adjoin (IsLocalRing.ResidueField ↥Ab)
        ({ModularCurve.jGeomGen (IsLocalRing.ResidueField ↥Ab) M, ModularCurve.jNGeomGen (IsLocalRing.ResidueField ↥Ab) M} :
          Set ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M))
        ≤ Algebra.adjoin (IsLocalRing.ResidueField ↥Ab) (Set.range ρ) :=
      Algebra.adjoin_le (Set.insert_subset_iff.mpr
        ⟨Algebra.subset_adjoin ⟨jChartFin A (↥K₂) j₂, hρj⟩,
         Set.singleton_subset_iff.mpr (Algebra.subset_adjoin ⟨jM, hρjM⟩)⟩)
    by_cases hs0 : s = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hfrs, hs0, div_zero]; simp
    · exact ⟨⟨r, hle hr⟩, ⟨s, hle hs⟩, hs0, by rw [hfrs, div_mul_cancel₀ _ hs0]⟩

  refine ⟨w, hss, ρ, ?_, hρϖ, hρj, fun b => hP₀ b, fun b => hP₀y b, hbir⟩
  intro b
  exact ⟨ψ (b : ↥K₂), hR1 b, hψ (b : ↥K₂), hρ b⟩

end S_ModularCurve_XZeroP_exists_mem_ssPlaces_ringHom_eq_residueFst_of_mem_ssJSet_chartAlgFin_twoChartIntegralModel_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroP_exists_mem_ssPlaces_ringHom_eq_residueFst_of_mem_ssJSet_chartAlgFin_twoChartIntegralModel_gamma0_mul (solution)
