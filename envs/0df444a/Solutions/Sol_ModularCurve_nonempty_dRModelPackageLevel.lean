-- Prove2me | solution 1 for ModularCurve.nonempty_dRModelPackageLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/95068658-bbfe-5ad6-b0c9-f3184907d59c

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_DRLevel_exists_cusps_involution_forgetful_smoothLocus
import Theorems.Thm_ModularCurve_DRLevel_exists_curveModel_iso_fibre0_chartPin
import Theorems.Thm_ModularCurve_DRLevel_exists_comp_pair_fibre
import Theorems.Thm_ModularCurve_DRLevel_placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul
import Theorems.Thm_ModularCurve_DRLevel_isReduced_pullback_comp
import Theorems.Thm_ModularCurve_DRLevel_exists_nodeEquiv_placeOfPoint_eq
import Theorems.Thm_ModularCurve_DRLevel_range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective
import Theorems.Thm_ModularCurve_IgusaScheme_locallyOfFinitePresentation_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_and_geometricallyIntegral_pullback_snd_igusaTo_rat
import Theorems.Thm_ModularCurve_IgusaScheme_exists_curveModel_iso_genericFibre_galoisCompat_chartPin
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_IgusaScheme_flat_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_pullback_igusaTo_specMap_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_dRModelPackageLevel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure"
p2m_attr_erase "instance" "instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst ModularCurve.coe_baseChangeRingHom ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve~nodeEquiv ModularCurve.IgusaScheme ModularCurve.DRLevel"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) :
    Nonempty (DRModelPackageLevel N₀ q hqN) := by
  classical

  obtain ⟨Meta, eeta, heetaIso, heeta, hgal, hMetaNe, hMetaPin⟩ :=
    ModularCurve.IgusaScheme.exists_curveModel_iso_genericFibre_galoisCompat_chartPin (N₀ * q) q
  obtain ⟨hsmooth, hgeom⟩ :=
    ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_and_geometricallyIntegral_pullback_snd_igusaTo_rat (N₀ * q) q

  obtain ⟨εinf, εzero, rhoInf, w, theta, π, iota0, iotaInf, U, hUrel, hrho, hεchart, hwover, hwinv, hws, htheta, hwchart,
      hiota, hpichart, hiotaInf, hpichartInf, hUmax, hεU, hε0U⟩ :=
    ModularCurve.DRLevel.exists_cusps_involution_forgetful_smoothLocus N₀ q hqN

  choose M e heIso hMne heM hMpin using
    (fun (κ : Type) (i1 : Field κ) (i2 : CharP κ q) (i3 : IsAlgClosed κ) (i4 : DecidableEq κ) (toκ : DRLevel.R q →+* κ) =>
      ModularCurve.DRLevel.exists_curveModel_iso_fibre0_chartPin N₀ q hqN κ toκ)

  choose comp hover hci hsurj hne hpi hcw using
    (fun (κ : Type) (i1 : Field κ) (i2 : CharP κ q) (i3 : IsAlgClosed κ) (i4 : DecidableEq κ) (toκ : DRLevel.R q →+* κ) =>
      ModularCurve.DRLevel.exists_comp_pair_fibre N₀ q hqN w hwover theta htheta hwchart π iota0 hiota hpichart κ toκ)

  have hfrob := fun (κ : Type) (i1 : Field κ) (i2 : CharP κ q) (i3 : IsAlgClosed κ) (i4 : DecidableEq κ) (toκ : DRLevel.R q →+* κ) =>
    @ModularCurve.DRLevel.placeOfPoint_comp_one_fibreMap0_eq_arithFrobC_smul N₀ q _ _ hqN
      w hwover theta htheta hwchart π iota0 hiota hpichart κ i1 i2 i3 i4 toκ
      (M κ i1 i2 i3 i4 toκ) (e κ i1 i2 i3 i4 toκ) (heIso κ i1 i2 i3 i4 toκ) (heM κ i1 i2 i3 i4 toκ) (hMne κ i1 i2 i3 i4 toκ) (hMpin κ i1 i2 i3 i4 toκ)
      (comp κ i1 i2 i3 i4 toκ) (hover κ i1 i2 i3 i4 toκ) (hci κ i1 i2 i3 i4 toκ) (hpi κ i1 i2 i3 i4 toκ) (hcw κ i1 i2 i3 i4 toκ)

  have hcross := fun (κ : Type) (i1 : Field κ) (i2 : CharP κ q) (i3 : IsAlgClosed κ) (i4 : DecidableEq κ) (toκ : DRLevel.R q →+* κ) =>
    @ModularCurve.DRLevel.isReduced_pullback_comp N₀ q _ _ hqN
      w hwover theta htheta hwchart π iota0 hiota hpichart κ i1 i2 i3 i4 toκ
      (comp κ i1 i2 i3 i4 toκ) (hover κ i1 i2 i3 i4 toκ) (hci κ i1 i2 i3 i4 toκ) (hpi κ i1 i2 i3 i4 toκ) (hcw κ i1 i2 i3 i4 toκ)

  choose nodeEquiv hnode using
    (fun (κ : Type) (i1 : Field κ) (i2 : CharP κ q) (i3 : IsAlgClosed κ) (i4 : DecidableEq κ) (toκ : DRLevel.R q →+* κ) =>
      @ModularCurve.DRLevel.exists_nodeEquiv_placeOfPoint_eq N₀ q _ _ hqN
        w hwover theta htheta hwchart π iota0 hiota hpichart κ i1 i2 i3 i4 toκ
        (M κ i1 i2 i3 i4 toκ) (e κ i1 i2 i3 i4 toκ) (heIso κ i1 i2 i3 i4 toκ) (heM κ i1 i2 i3 i4 toκ) (hMne κ i1 i2 i3 i4 toκ) (hMpin κ i1 i2 i3 i4 toκ)
        (comp κ i1 i2 i3 i4 toκ) (hover κ i1 i2 i3 i4 toκ) (hci κ i1 i2 i3 i4 toκ) (hpi κ i1 i2 i3 i4 toκ) (hcw κ i1 i2 i3 i4 toκ) (hfrob κ i1 i2 i3 i4 toκ))

  have hcusp := fun (κ : Type) (i1 : Field κ) (i2 : CharP κ q) (i3 : IsAlgClosed κ) (i4 : DecidableEq κ) (toκ : DRLevel.R q →+* κ) =>
    @ModularCurve.DRLevel.range_sectionFibre_cusps_subset_range_comp_of_jointlySurjective N₀ q _ _ hqN
      εinf εzero rhoInf hrho hεchart w hwover theta htheta hwchart hws π iota0 hiota hpichart iotaInf hiotaInf hpichartInf
      κ i1 i2 i3 i4 toκ (comp κ i1 i2 i3 i4 toκ) (hover κ i1 i2 i3 i4 toκ) (hci κ i1 i2 i3 i4 toκ) (hsurj κ i1 i2 i3 i4 toκ) (hpi κ i1 i2 i3 i4 toκ) (hcw κ i1 i2 i3 i4 toκ)

  exact ⟨{

    isProper := by
      obtain ⟨h1, h2⟩ := ModularCurve.IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (N₀ * q) q
      haveI := h1; haveI := h2
      exact ModularCurve.IgusaScheme.isProper_igusaTo (N₀ * q) q
    flat := ModularCurve.IgusaScheme.flat_igusaTo (N₀ * q) q
    isIntegral := ModularCurve.IgusaScheme.isIntegral (N₀ * q) q
    lfp := ModularCurve.IgusaScheme.locallyOfFinitePresentation_igusaTo (N₀ * q) q
    normal := fun U hU => ModularCurve.IgusaScheme.isIntegrallyClosed_sections_of_isAffineOpen (N₀ * q) q U hU

    Meta := Meta
    eeta := eeta
    eeta_iso := heetaIso
    heeta := heeta
    hgal := hgal
    Meta_chart_nonempty := hMetaNe
    Meta_pin := hMetaPin
    smooth_generic := hsmooth
    geomIntegral_generic := hgeom

    εinf := εinf
    εzero := εzero
    rhoInf := rhoInf
    rhoInf_spec := hrho
    εinf_chart := hεchart
    w := w
    w_over := hwover
    w_invol := hwinv
    w_sections := hws
    theta := theta
    theta_spec := htheta
    w_chart := hwchart
    π := π
    iota0 := iota0
    iota0_spec := hiota
    pi_chart := hpichart

    smoothLocus := U
    smoothLocus_relDim := hUrel
    smoothLocus_maximal := hUmax
    εinf_mem_smoothLocus := hεU
    εzero_mem_smoothLocus := hε0U

    fibre_reduced := @fun κ i1 i2 i3 i4 toκ => by
      letI := toκ.toAlgebra
      exact ModularCurve.IgusaScheme.isReduced_pullback_igusaTo_specMap_of_not_dvd N₀ q hqN κ
    Mfib := @fun κ i1 i2 i3 i4 toκ => M κ i1 i2 i3 i4 toκ
    efib := @fun κ i1 i2 i3 i4 toκ => e κ i1 i2 i3 i4 toκ
    efib_iso := @fun κ i1 i2 i3 i4 toκ => heIso κ i1 i2 i3 i4 toκ
    hefib := @fun κ i1 i2 i3 i4 toκ => heM κ i1 i2 i3 i4 toκ
    Mfib_chart_nonempty := @fun κ i1 i2 i3 i4 toκ => hMne κ i1 i2 i3 i4 toκ
    Mfib_pin := @fun κ i1 i2 i3 i4 toκ => hMpin κ i1 i2 i3 i4 toκ
    comp := @fun κ i1 i2 i3 i4 toκ => comp κ i1 i2 i3 i4 toκ
    comp_over := @fun κ i1 i2 i3 i4 toκ => hover κ i1 i2 i3 i4 toκ
    comp_isClosedImmersion := @fun κ i1 i2 i3 i4 toκ => hci κ i1 i2 i3 i4 toκ
    comp_jointly_surjective := @fun κ i1 i2 i3 i4 toκ => hsurj κ i1 i2 i3 i4 toκ
    range_comp_ne := @fun κ i1 i2 i3 i4 toκ => hne κ i1 i2 i3 i4 toκ
    comp_pi := @fun κ i1 i2 i3 i4 toκ => hpi κ i1 i2 i3 i4 toκ
    comp1_pi_place := @fun κ i1 i2 i3 i4 toκ => hfrob κ i1 i2 i3 i4 toκ
    comp_w := @fun κ i1 i2 i3 i4 toκ => hcw κ i1 i2 i3 i4 toκ
    εinf_mem_comp0 := @fun κ i1 i2 i3 i4 toκ => (hcusp κ i1 i2 i3 i4 toκ).1
    εzero_mem_comp1 := @fun κ i1 i2 i3 i4 toκ => (hcusp κ i1 i2 i3 i4 toκ).2.1

    crossing_reduced := @fun κ i1 i2 i3 i4 toκ => hcross κ i1 i2 i3 i4 toκ
    nodeEquiv := @fun κ i1 i2 i3 i4 toκ => nodeEquiv κ i1 i2 i3 i4 toκ
    node_pin := @fun κ i1 i2 i3 i4 toκ => hnode κ i1 i2 i3 i4 toκ

    iotaInf := iotaInf
    iotaInf_spec := hiotaInf
    pi_chartInf := hpichartInf
    εinf0_comp0 := @fun κ i1 i2 i3 i4 toκ => (hcusp κ i1 i2 i3 i4 toκ).2.2.1
    εinf0_comp1 := @fun κ i1 i2 i3 i4 toκ => (hcusp κ i1 i2 i3 i4 toκ).2.2.2 }⟩

end S_ModularCurve_nonempty_dRModelPackageLevel
end P2MW
export P2MW.S_ModularCurve_nonempty_dRModelPackageLevel (solution)
