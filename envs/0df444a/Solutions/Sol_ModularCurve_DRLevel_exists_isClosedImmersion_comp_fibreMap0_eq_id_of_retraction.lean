-- Prove2me | solution 1 for ModularCurve.DRLevel.exists_isClosedImmersion_comp_fibreMap0_eq_id_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2f17a860-7cdf-5991-844d-aed208759eff

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_residue
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegral_pullback_igusaTo_of_charP
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_igusaTo
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRLevel_exists_isClosedImmersion_comp_fibreMap0_eq_id_of_retraction
p2m_attr_erase "instance" "instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRLevel_exists_isClosedImmersion_comp_fibreMap0_eq_id_of_retraction.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel P2MW.S_ModularCurve_DRLevel_exists_isClosedImmersion_comp_fibreMap0_eq_id_of_retraction.ModularCurve.DRLevel"
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase DRLevel.toBase0 DRLevel.fibre DRLevel.fibre0 DRLevel.fibreMap0 IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin modularFunctionFieldFull IgusaScheme.smoothOfRelativeDimension_one_pullback_residue IgusaScheme.isIntegral_pullback_igusaTo_of_charP IgusaScheme.isProper_igusaTo IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf"
namespace DRLevel
p2m_export "ModularCurve.DRLevel" "R X toBase toBase0 fibre fibre0 fibreMap0"
namespace SectionComp
p2m_open "ModularCurve.DRLevel ModularCurve"

theorem range_subset_of_isOpen {A : Type} [CommRing A] [IsLocalRing A] {Y : Scheme.{0}}
    (f : Spec (CommRingCat.of A) ⟶ Y) {U : Set Y} (hU : IsOpen U)
    (h : f (IsLocalRing.closedPoint A) ∈ U) : Set.range f ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map f.continuous).mem_open hU h

section Chart

variable (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (κ : Type) [CommRing κ] [Algebra (R q) κ]

theorem isPullback_chart
    (c : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
      pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))))) :
    IsPullback c (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom)) (pullback.fst _ _) (ιFin N q) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd _ _)
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))) (h₂₂ := igusaTo N q) ?_ hcfst
    (IsPullback.of_hasPullback _ _).flip
  rw [hcsnd, ιFin_igusaTo]
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct (R q) κ ↥(chartAlgFin N q))

theorem isOpenImmersion_chart
    (c : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
      pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))))) :
    IsOpenImmersion c := by
  rw [← (isPullback_chart N q κ c hcfst hcsnd).isoPullback_hom_fst]
  infer_instance

theorem mem_range_chart
    (c : Spec (CommRingCat.of (κ ⊗[R q] ↥(chartAlgFin N q))) ⟶
      pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q))).toRingHom) ≫ ιFin N q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R q) (A := κ) (B := ↥(chartAlgFin N q)))))
    (x : ↥(pullback (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))))
    (hx : (pullback.fst (igusaTo N q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) x ∈ Set.range (ιFin N q)) : x ∈ Set.range c := by
  have H := isPullback_chart N q κ c hcfst hcsnd
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst (igusaTo N q)
      (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) (ιFin N q)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, rfl⟩ := hx'
  exact ⟨H.isoPullback.inv t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

end Chart

theorem isDominant_of_isOpenImmersion {U X : Scheme.{0}} [IrreducibleSpace X] (f : U ⟶ X) [IsOpenImmersion f]
    [Nonempty U] : IsDominant f := by
  refine ⟨?_⟩
  have hη : genericPoint X ∈ Set.range f.base :=
    ((genericPoint_spec X).mem_open_set_iff f.isOpenEmbedding.isOpen_range).mpr (by simpa using Set.range_nonempty _)
  intro y
  have : y ∈ closure ({genericPoint X} : Set X) := by
    rw [(genericPoint_spec X).def]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr hη) this

end ModularCurve.DRLevel.SectionComp

open ModularCurve.DRLevel.SectionComp in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

    (π : SchemeHomOver (DRLevel.toBase N₀ q) (DRLevel.toBase0 N₀ q))
    (iota0 : ↥(IgusaScheme.chartAlgFin N₀ q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hiota : ∀ b, (((iota0 b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
      ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ))
    (hpichart : IgusaScheme.ιFin (N₀ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ IgusaScheme.ιFin N₀ q)

    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (DRLevel.R q) κ]

    [Nontrivial (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))]

    (c₀ : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))) ⟶
      DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q))).toRingHom) ≫ IgusaScheme.ιFin N₀ q)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin N₀ q)))))
    (c : Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ⟶
      DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q))).toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := DRLevel.R q) (A := κ) (B := ↥(IgusaScheme.chartAlgFin (N₀ * q) q)))))

    (σ₀ : κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[κ] κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q))
    (hσ₀ : ∀ z, σ₀ (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0 z) = z) :
    ∃ comp₀ : DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ) ⟶ DRLevel.fibre (N₀ := N₀) (algebraMap (DRLevel.R q) κ),
      comp₀ ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      IsClosedImmersion comp₀ ∧
      comp₀ ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _ ∧
      c₀ ≫ comp₀ = Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c ∧

      (∀ x, comp₀.base x ∈ Set.range c.base → x ∈ Set.range c₀.base) := by
  classical

  haveI hint0 : IsIntegral ↑(DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) :=
    IgusaScheme.isIntegral_pullback_igusaTo_of_charP N₀ q hqN κ
  haveI hsm0 : SmoothOfRelativeDimension 1
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) :=
    IgusaScheme.smoothOfRelativeDimension_one_pullback_residue N₀ q hqN κ (algebraMap (DRLevel.R q) κ)
  obtain ⟨hft1, hft2⟩ := IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf (N₀ * q) q
  obtain ⟨hft3, hft4⟩ := IgusaScheme.finiteType_chartAlgFin_and_chartAlgInf N₀ q
  haveI := hft1; haveI := hft2; haveI := hft3; haveI := hft4
  haveI hprop : IsProper (DRLevel.toBase N₀ q) := IgusaScheme.isProper_igusaTo (N₀ * q) q
  haveI hprop0 : IsProper (DRLevel.toBase0 N₀ q) := IgusaScheme.isProper_igusaTo N₀ q
  haveI hcO : IsOpenImmersion c := isOpenImmersion_chart (N₀ * q) q κ c hcfst hcsnd
  haveI hc₀O : IsOpenImmersion c₀ := isOpenImmersion_chart N₀ q κ c₀ hc₀fst hc₀snd
  haveI hne : Nonempty ↥(Spec (CommRingCat.of (κ ⊗[DRLevel.R q] ↥(IgusaScheme.chartAlgFin N₀ q)))) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

  have hcπ : c ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) ≫ c₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hc₀fst, DRLevel.fibreMap0, pullback.lift_fst, ← Category.assoc, hcfst,
        Category.assoc, hpichart, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
    · rw [Category.assoc, Category.assoc, hc₀snd, DRLevel.fibreMap0, pullback.lift_snd, ← Category.assoc, hcsnd,
        Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeftRingHom_apply]

  have hσSpec : Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) iota0).toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1
    rw [← CommRingCat.ofHom_id]
    congr 1
    exact RingHom.ext fun z => hσ₀ z

  have hf : (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c) ≫
      pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))) =
      c₀ ≫ pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))) := by
    rw [Category.assoc, hcsnd, hc₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [show a ⊗ₜ[DRLevel.R q] (1 : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = algebraMap κ _ a by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply],
      AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

  have hηmem : genericPoint ↑(DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)) ∈ Set.range c₀.base :=
    ((genericPoint_spec _).mem_open_set_iff c₀.isOpenEmbedding.isOpen_range).mpr (by simpa using Set.range_nonempty _)
  have hreg : ∀ x : ↑(DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)), x ∉ Set.range c₀.base →
      IsDiscreteValuationRing ((DRLevel.fibre0 (N₀ := N₀) (algebraMap (DRLevel.R q) κ)).presheaf.stalk x) := by
    intro x hx
    have hxη : x ≠ genericPoint _ := fun h => hx (h ▸ hηmem)
    exact SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) x
      (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
        (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) x hxη)

  obtain ⟨comp₀, hover, hchart⟩ :=
    AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_isProper_of_isDiscreteValuationRing_stalk
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) c₀ hreg
      (pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))))
      (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c) hf

  have hπsnd : DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) ≫
      pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))) =
      pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))) := by
    rw [DRLevel.fibreMap0, pullback.lift_snd, Category.comp_id]
  haveI : IsDominant c₀ := isDominant_of_isOpenImmersion c₀
  have hsec : comp₀ ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) = 𝟙 _ := by
    refine ext_of_isDominant_of_isSeparated
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) ?_ c₀ ?_
    · rw [Category.assoc, hπsnd, hover, Category.id_comp]
    · rw [← Category.assoc, hchart, Category.assoc, hcπ, ← Category.assoc, hσSpec, Category.id_comp, Category.comp_id]

  haveI : IsSeparated (DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)) := by
    haveI : IsSeparated (DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ) ≫
        pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ)))) := by
      rw [hπsnd]; infer_instance
    exact IsSeparated.of_comp _
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R q) κ))))
  have hci : IsClosedImmersion comp₀ := by
    haveI : IsClosedImmersion (comp₀ ≫ DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)) := by
      rw [hsec]; infer_instance
    exact IsClosedImmersion.of_comp comp₀ (DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ))

  refine ⟨comp₀, hover, hci, hsec, hchart, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx
  have h1 : x = (DRLevel.fibreMap0 π (algebraMap (DRLevel.R q) κ)).base (comp₀.base x) := by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  rw [h1, ← hy, ← Scheme.Hom.comp_apply, hcπ, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end S_ModularCurve_DRLevel_exists_isClosedImmersion_comp_fibreMap0_eq_id_of_retraction
end P2MW
export P2MW.S_ModularCurve_DRLevel_exists_isClosedImmersion_comp_fibreMap0_eq_id_of_retraction (solution)
