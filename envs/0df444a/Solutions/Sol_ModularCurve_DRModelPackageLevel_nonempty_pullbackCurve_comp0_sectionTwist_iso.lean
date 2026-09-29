-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_pullbackCurve_comp0_sectionTwist_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/95395835-c4fd-540f-b615-fbfb5a626415

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_charP
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackCurve_comp0_sectionTwist_iso
p2m_attr_erase "instance" "instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve IsLocalRing ModularCurve ModularCurve.DRLevel"

noncomputable section

namespace RTwist

section foldr
variable {X : Scheme.{u}} {ι : Type*}

abbrev twistStep (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (M : X.Modules) : X.Modules :=
  (K i ^ pos i).invModule ⊗ (K i ^ neg i).module ⊗ M

def foldrTwistCongr (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅ l.foldr (twistStep K pos neg) M'
  | [], _, _, e => e
  | (i :: l), _, _, e => whiskerLeftIso _ (whiskerLeftIso _ (foldrTwistCongr K pos neg l e))

theorem isInvertible_pow {I : X.IdealSheafData} (hI : I.IsInvertible) : ∀ n : ℕ, (I ^ n).IsInvertible
  | 0 => by
    rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | (n + 1) => by
    rw [pow_succ]
    exact (isInvertible_pow hI n).mul hI

theorem top_pow (n : ℕ) : (⊤ : X.IdealSheafData) ^ n = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

theorem isInvertible_foldrTwist (K : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (hK : ∀ i, (K i).IsInvertible) :
    ∀ (l : List ι) {M : X.Modules} (_ : Scheme.Modules.IsInvertible M),
      Scheme.Modules.IsInvertible (l.foldr (twistStep K pos neg) M)
  | [], _, hM => hM
  | (i :: l), _, hM =>
    (isInvertible_pow (hK i) (pos i)).isInvertible_invModule.tensor
      ((isInvertible_pow (hK i) (neg i)).isInvertible_module.tensor (isInvertible_foldrTwist K pos neg hK l hM))

end foldr

section top
variable {X : Scheme.{u}}

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (V : Z.Opens) :
    Subsingleton Γ(Z, V) := by
  obtain rfl : V = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

theorem unitToPushforwardUnit_eq_zero_of_isEmpty {Z : Scheme.{u}} (i : Z ⟶ X) [IsEmpty Z] :
    i.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  haveI : Subsingleton Γ(Z, i ⁻¹ᵁ U.unop) := subsingleton_sections_of_isEmpty _
  exact Subsingleton.elim (α := Γ(Z, i ⁻¹ᵁ U.unop)) _ _

def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (unitToPushforwardUnit_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι) ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

theorem nonempty_topInvModuleIso : Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) :=
  MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit (topModuleIso (X := X))
    (Scheme.IdealSheafData.isInvertible_top (X := X)).nonempty_module_tensor_invModule_iso.1 ⟨λ_ _⟩

def topInvModuleIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules := nonempty_topInvModuleIso.some

def twistStepTopIso {ι : Type*} (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = ⊤)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ M' :=
  ((eqToIso (by rw [hi, top_pow]) : (K i ^ pos i).invModule ≅ (⊤ : X.IdealSheafData).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi, top_pow]) : (K i ^ neg i).module ≅ (⊤ : X.IdealSheafData).module) ⊗ᵢ e)) ≪≫
    ((topInvModuleIso ⊗ᵢ (topModuleIso ⊗ᵢ Iso.refl M')) ≪≫ ((λ_ _) ≪≫ (λ_ _)))

def twistStepCongr {ι : Type*} (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = K' i)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ twistStep K' pos neg i M' :=
  ((eqToIso (by rw [hi]) : (K i ^ pos i).invModule ≅ (K' i ^ pos i).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi]) : (K i ^ neg i).module ≅ (K' i ^ neg i).module) ⊗ᵢ e))

def foldrTwistSelectIso {ι : Type*} {κ : Type*} [DecidableEq κ] (c : ι → κ) (j : κ)
    (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (h₁ : ∀ i, c i = j → K i = K' i) (h₂ : ∀ i, c i ≠ j → K i = ⊤) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅
        l.foldr (fun i N => if c i = j then twistStep K' pos neg i N else N) M'
  | [], _, _, e => e
  | (i :: l), M, M', e => by
    by_cases hc : c i = j
    · refine twistStepCongr K K' pos neg i (h₁ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_pos hc]
    · refine twistStepTopIso K pos neg i (h₂ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_neg hc]

end top

section rigid
variable {A : Type u} [CommRing A] [IsLocalRing A] {P : Scheme.{u}}

theorem nonempty_rigidify_iso_self (σ : Spec (CommRingCat.of A) ⟶ P) (q : P ⟶ Spec (CommRingCat.of A))
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨eD⟩ := ((hL.pullback σ).dual).1.nonempty_iso_tensorUnit_of_isLocalRing
  exact ⟨whiskerLeftIso L ((Scheme.Modules.pullback q).mapIso eD ≪≫ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L⟩

end rigid

section geom
variable {X₀ X T : Scheme.{u}}

theorem comap_ker_eq_ker_of_isPullback {Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem comap_ker_hom_of_iso (e : X₀ ≅ X) (y : T ⟶ X) [IsClosedImmersion y] :
    y.ker.comap e.hom = (y ≫ e.inv).ker :=
  comap_ker_eq_ker_of_isPullback (iX := y ≫ e.inv) (g := 𝟙 T) (IsPullback.of_vert_isIso ⟨by simp⟩)

theorem isIso_snd_of_subset_range (χ : X₀ ⟶ X) [IsClosedImmersion χ] [IsReduced X] (U : X.Opens)
    (hU : (U : Set X) ⊆ Set.range χ.base) : IsIso (pullback.snd χ U.ι) := by
  haveI : IsReduced (U : Scheme.{u}) := isReduced_of_isOpenImmersion U.ι
  haveI : Surjective (pullback.snd χ U.ι) := ⟨by
    intro u
    have h1 : U.ι.base u ∈ Set.range χ.base :=
      hU (by rw [← Scheme.Opens.range_ι U]; exact ⟨u, rfl⟩)
    have h2 : u ∈ Set.range (pullback.snd χ U.ι).base := by
      rw [Scheme.Pullback.range_snd]; exact h1
    exact h2⟩
  exact isIso_of_isClosedImmersion_of_surjective _

theorem isPullback_of_subset_range (χ : X₀ ⟶ X) [IsClosedImmersion χ] [IsReduced X] (U : X.Opens)
    (hU : (U : Set X) ⊆ Set.range χ.base) (y : T ⟶ X) (hy : Set.range y.base ⊆ (U : Set X))
    (z : T ⟶ X₀) (hz : z ≫ χ = y) : IsPullback z (𝟙 T) χ y := by
  have hy' : Set.range y.base ⊆ Set.range U.ι.base := by rwa [Scheme.Opens.range_ι]
  obtain ⟨y', rfl⟩ : ∃ y' : T ⟶ U, y' ≫ U.ι = y :=
    ⟨IsOpenImmersion.lift U.ι y hy', IsOpenImmersion.lift_fac _ _ _⟩
  haveI := isIso_snd_of_subset_range χ U hU
  haveI : IsIso ((pullbackLeftPullbackSndIso χ U.ι y').hom ≫ pullback.snd χ (y' ≫ U.ι)) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
    infer_instance
  haveI : IsIso (pullback.snd χ (y' ≫ U.ι)) :=
    IsIso.of_isIso_comp_left (pullbackLeftPullbackSndIso χ U.ι y').hom (pullback.snd χ (y' ≫ U.ι))
  let l : T ⟶ pullback χ (y' ≫ U.ι) := pullback.lift z (𝟙 T) (by rw [hz, Category.id_comp])
  have hl : l ≫ pullback.snd _ _ = 𝟙 T := pullback.lift_snd _ _ _
  haveI : IsIso (l ≫ pullback.snd _ _) := by rw [hl]; infer_instance
  haveI : IsIso l := IsIso.of_isIso_comp_right l (pullback.snd _ _)
  exact IsPullback.of_iso_pullback ⟨by rw [hz, Category.id_comp]⟩ (asIso l)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem ker_eq_top_of_isEmpty (f : X₀ ⟶ X) [QuasiCompact f] [IsEmpty X₀] : f.ker = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  have hx' : x ∈ closure (Set.range f.base) := by
    rw [← Scheme.Hom.support_ker]; exact hx
  rw [Set.range_eq_empty, closure_empty] at hx'
  exact hx'

theorem comap_ker_eq_top_of_disjoint (χ : X₀ ⟶ X) (y : T ⟶ X) [IsClosedImmersion y]
    (h : ∀ (t : T) (x₀ : X₀), χ.base x₀ ≠ y.base t) : y.ker.comap χ = ⊤ := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  haveI : IsEmpty ↥(pullback χ y) := ⟨fun q => h ((pullback.snd χ y).base q) ((pullback.fst χ y).base q) (by
    have := congrArg (fun g => g.base q) (pullback.condition (f := χ) (g := y))
    simpa using this)⟩
  exact ker_eq_top_of_isEmpty _

end geom

end RTwist

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem RTwist.core
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    haveI : IsProper (toBase N₀ p) := 𝔓.isProper
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))] (j : Fin 2)
      {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)))
      (c : Fin n → Fin 2)
      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))))
      (_ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (s i).1)
      (_ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)
      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (_ : ∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i)
      (_ : ∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base)
      (ψred : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Spec.map (CommRingCat.ofHom ρ)))
      (_ : ψred.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
      (pos neg : Fin n → ℕ),
      Nonempty ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j) (𝟙 _))).obj
        ((Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).obj
          ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).obj
            (Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
            (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))) ≅
        ((List.finRange n).foldr
          (fun i M => if c i = j then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _))) := by
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  haveI : IsProper (toBase N₀ p) := 𝔓.isProper
  intro _iP0 j n s hs c y hy₁ hy₂ z hz hzy hyn ψred hψ pos neg
  classical

  haveI hsm0 : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) :=
    ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_charP N₀ p hpN₀ (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))

  have key₁ : ∀ j k : Fin 2, k ≠ 1 - j → k = j := by decide
  have key₂ : ∀ j k : Fin 2, k ≠ j → 1 - k = j := by decide

  let K : Fin n → (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).IdealSheafData := fun i => (RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I
  let K' : Fin n → (pullback (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).IdealSheafData := fun i =>
    (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I

  let χ : pullback (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) ⟶ pullback (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) := curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let eκ := BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let Φ₂ : pullback (toBase N₀ p) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))) ≫ specMap (R p) (ResidueField ↥A)) ⟶ pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) := baseChangeSnd (toBase N₀ p) ψred
  let Φ := (χ ≫ eκ.hom) ≫ Φ₂

  let pr : pullback (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) ⟶ _ := pullback.fst (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let pr0 : pullback (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) ⟶ _ := pullback.fst (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  let ytil : ∀ i : Fin n, (Spec (CommRingCat.of (ResidueField ↥A))) ⟶ pullback (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) := fun i => graphOver (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (y i) (hy₂ i)
  have hχpr : χ ≫ pr = pr0 ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j := by
    simp only [χ, pr, pr0, curveChange, pullback.lift_fst]
  have hχsnd : χ ≫ pullback.snd (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) = pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) := curveChange_snd _ _ _
  have hytil_pr : ∀ i, ytil i ≫ pr = y i := fun i => graphOver_fst _ _ _

  have hab : ∀ i, ((K i).comap Φ₂).comap eκ.hom = (ytil i).ker := by
    intro i
    have ha : (K i).comap Φ₂ =
        (graphOver (toBase N₀ p) (ψred.1 ≫ (s i).1) (by rw [Category.assoc, (s i).2, ψred.2])).ker :=
      congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint (toBase N₀ p) (s i).1 (s i).2 ψred.1 ψred.2)
    rw [ha, RTwist.comap_ker_hom_of_iso]
    congr 1
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc, hy₁ i, hψ]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]

  haveI : IsClosedImmersion (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j) := 𝔓.comp_isClosedImmersion (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j
  haveI : IsClosedImmersion (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - j)) := 𝔓.comp_isClosedImmersion (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - j)
  haveI hχci : IsClosedImmersion χ :=
    MorphismProperty.pullback_map (P := @IsClosedImmersion) (f := (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))) (g := 𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (f' := (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)))
      (g' := 𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (i₁ := 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j) (i₂ := 𝟙 _) inferInstance inferInstance
      (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j).symm (Category.id_comp _).symm
  haveI : IsReduced (pullback (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) := by
    haveI := 𝔓.fibre_reduced (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))
    exact isReduced_of_isOpenImmersion pr

  let Uc : (fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))).Opens :=
    ⟨(Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - j)).base)ᶜ, (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - j)).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U : (pullback (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))).Opens := pr ⁻¹ᵁ Uc
  have hU : (U : Set _) ⊆ Set.range χ.base := by
    intro u hu
    have hu' : pr.base u ∉ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - j)).base := hu
    obtain ⟨k, x0, hx0⟩ : ∃ (k : Fin 2) (x0 : _), (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) k).base x0 = pr.base u := by
      rcases 𝔓.comp_jointly_surjective (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (pr.base u) with ⟨x, hx⟩ | ⟨x, hx⟩
      exacts [⟨0, x, hx⟩, ⟨1, x, hx⟩]
    obtain rfl : k = j := key₁ j k (by rintro rfl; exact hu' ⟨x0, hx0⟩)
    obtain ⟨q, rfl⟩ := (Scheme.homeoOfIso (asIso pr0)).surjective x0
    refine ⟨q, (Scheme.homeoOfIso (asIso pr)).injective ?_⟩
    change pr.base (χ.base q) = pr.base u
    rw [← Scheme.Hom.comp_apply, hχpr, Scheme.Hom.comp_apply]
    exact hx0
  have hyU : ∀ i, c i = j → Set.range (ytil i).base ⊆ (U : Set _) := by
    rintro i hci _ ⟨t, rfl⟩
    obtain rfl : t = IsLocalRing.closedPoint (ResidueField ↥A) := Subsingleton.elim _ _
    change pr.base ((ytil i).base _) ∉ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - j)).base
    rw [← Scheme.Hom.comp_apply, hytil_pr, ← hci]
    exact hyn i

  have hgeo : ∀ i, c i = j → (ytil i).ker.comap χ = K' i := by
    intro i hci
    refine RTwist.comap_ker_eq_ker_of_isPullback (RTwist.isPullback_of_subset_range χ U hU (ytil i) (hyU i hci)
      (graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)) ?_)
    apply pullback.hom_ext
    · rw [Category.assoc, hχpr, graphOver_fst_assoc, hytil_pr, ← hci, hzy i]
    · rw [Category.assoc, hχsnd, graphOver_snd, graphOver_snd]
  have htop : ∀ i, c i ≠ j → (ytil i).ker.comap χ = ⊤ := by
    intro i hci
    apply RTwist.comap_ker_eq_top_of_disjoint
    intro t x0 hx
    obtain rfl : t = IsLocalRing.closedPoint (ResidueField ↥A) := Subsingleton.elim _ _
    have h1 : pr.base (χ.base x0) ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) j).base :=
      ⟨pr0.base x0, by rw [← Scheme.Hom.comp_apply, ← hχpr, Scheme.Hom.comp_apply]⟩
    rw [hx, ← Scheme.Hom.comp_apply, hytil_pr, ← key₂ j (c i) hci] at h1
    exact hyn i h1
  have hKΦ₁ : ∀ i, c i = j → (K i).comap Φ = K' i := by
    intro i hci
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hab, hgeo i hci]
  have hKΦ₂ : ∀ i, c i ≠ j → (K i).comap Φ = ⊤ := by
    intro i hci
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hab, htop i hci]

  have hKinv : ∀ i, (K i).IsInvertible := by
    intro i
    let W : (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Opens := pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ 𝔓.smoothLocus
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
    haveI : SmoothOfRelativeDimension 1 (W.ι ≫ pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
        ((isPullback_morphismRestrict (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) 𝔓.smoothLocus).paste_vert
          (IsPullback.of_hasPullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)))) inferInstance
    refine Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) W
      (graphOver (toBase N₀ p) (s i).1 (s i).2) (graphOver_snd _ _ _) ?_
    change (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).base ((graphOver (toBase N₀ p) (s i).1 (s i).2).base _) ∈ (𝔓.smoothLocus : Set (X N₀ p))
    rw [← Scheme.Hom.comp_apply, graphOver_fst]
    exact hs i ⟨_, rfl⟩
  have hK'inv : ∀ i, ((K i).comap Φ).IsInvertible := by
    intro i
    by_cases hci : c i = j
    · rw [hKΦ₁ i hci]
      exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))))
        (graphOver (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)) (graphOver_snd _ _ _)
    · rw [hKΦ₂ i hci]
      exact Scheme.IdealSheafData.isInvertible_top

  have h1inv : ∀ (Y : Scheme.{0}), (1 : Y.IdealSheafData).IsInvertible := fun Y => by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  let C0 : Fin 0 → (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).IdealSheafData := fun _ => ⊤
  let a0 : Fin 0 → ℕ := fun _ => 0
  have hprod : (∏ F, C0 F ^ a0 F) = 1 := Fintype.prod_empty _
  have hprod' : (∏ F, (C0 F).comap Φ ^ a0 F) = 1 := Fintype.prod_empty _
  obtain ⟨eB⟩ : Nonempty ((∏ F, C0 F ^ a0 F).invModule ⊗ (∏ F, C0 F ^ a0 F).module ≅ 𝟙_ _) := by
    rw [hprod]; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
  obtain ⟨eB'⟩ : Nonempty ((∏ F, (C0 F).comap Φ ^ a0 F).invModule ⊗ (∏ F, (C0 F).comap Φ ^ a0 F).module ≅ 𝟙_ _) := by
    rw [hprod']; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
  have hL : Scheme.Modules.IsInvertible ((List.finRange n).foldr (RTwist.twistStep K pos neg) (𝟙_ _)) :=
    RTwist.isInvertible_foldrTwist K pos neg hKinv _ (Scheme.Modules.isInvertible_unit _)
  obtain ⟨erig⟩ := RTwist.nonempty_rigidify_iso_self (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf) (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) hL
  obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso Φ K pos neg C0 a0 a0 hKinv
    (fun F => F.elim0) hK'inv (fun F => F.elim0)
  refine ⟨(Scheme.Modules.pullbackComp χ eκ.hom).app _ ≪≫ (Scheme.Modules.pullbackComp (χ ≫ eκ.hom) Φ₂).app _ ≪≫
    (Scheme.Modules.pullback Φ).mapIso (erig ≪≫ RTwist.foldrTwistCongr K pos neg _ eB.symm) ≪≫ e4 ≪≫
    RTwist.foldrTwistCongr _ pos neg _ eB' ≪≫
    RTwist.foldrTwistSelectIso c j (fun i => (K i).comap Φ) K' pos neg hKΦ₁ hKΦ₂ _ (Iso.refl _)⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    haveI : IsProper (toBase N₀ p) := 𝔓.isProper
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)))
      (c : Fin n → Fin 2)

      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))))
      (_ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (s i).1)
      (_ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)

      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (_ : ∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i)
      (_ : ∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base)

      (ψred : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Spec.map (CommRingCat.ofHom ρ)))
      (_ : ψred.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)))
      (pos neg : Fin n → ℕ),
      Nonempty ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝟙 _))).obj
        ((Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).obj
          ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).obj
            (Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
            (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))) ≅
        ((List.finRange n).foldr
          (fun i M => if c i = 0 then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _))) := by
  intro _iP0 n s hs c y hy₁ hy₂ z hz hzy hyn ψred hψ pos neg
  exact RTwist.core N₀ p hpN₀ 𝔓 A hA ρ hρ 0 s hs c y hy₁ hy₂ z hz hzy hyn ψred hψ pos neg

end

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_nonempty_pullbackCurve_comp0_sectionTwist_iso
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_pullbackCurve_comp0_sectionTwist_iso (solution)
