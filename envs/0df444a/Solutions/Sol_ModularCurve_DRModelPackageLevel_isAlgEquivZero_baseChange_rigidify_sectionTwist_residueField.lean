-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isAlgEquivZero_baseChange_rigidify_sectionTwist_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/18f95ab6-21da-5ca1-a59b-4b452e210ee9

import Mathlib
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackCurve_comp0_sectionTwist_iso
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field
import Theorems.Thm_AlgebraicGeometry_RelPicard_preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
import Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isInvertible_sectionTwist
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isAlgEquivZero_baseChange_rigidify_sectionTwist_residueField
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap"
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_isAlgEquivZero_baseChange_rigidify_sectionTwist_residueField.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel"

section PTEXT
open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback IsClosedImmersion.of_comp Scheme.Hom GeometricallyIntegral Scheme.Hom.stalkMap_congr_point_assoc stalkClosedPointIso Scheme.Hom.stalkMap_congr_hom LocallyOfFiniteType Spec IsIntegral Scheme.Hom.stalkMap_comp Spec.map Scheme Smooth Scheme.stalkClosedPointTo pointEquivClosedPoint IsClosedImmersion IsSeparated Scheme.Modules SpecToEquivOfLocalRing_eq_iff pointEquivClosedPoint_apply_coe Scheme.Hom.stalkMap_id Scheme.Pullback.exists_preimage_pullback SpecToEquivOfLocalRing Scheme.Hom.comp_apply Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.RigidifiedLineBundle Scheme.Modules.rigidify RelEffCartierDiv RelEffCartierDiv.ofPoint RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves geometricallyIntegral_of_isAlgClosed RelEffCartierDiv.isInvertible_I"
p2m_open "AlgebraicGeometry"

theorem RingHom.eq_of_isLocalRing_of_comp_eq_id
    {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    (φ ψ : A →+* K) (ι : K →+* A)
    (hφ : φ.comp ι = RingHom.id K) (hψ : ψ.comp ι = RingHom.id K) : φ = ψ := by
  have hφs : Function.Surjective φ := fun k => ⟨ι k, by simpa using RingHom.congr_fun hφ k⟩
  have hψs : Function.Surjective ψ := fun k => ⟨ι k, by simpa using RingHom.congr_fun hψ k⟩
  have hker : RingHom.ker φ = RingHom.ker ψ := by
    rw [IsLocalRing.ker_eq_maximalIdeal φ hφs, IsLocalRing.ker_eq_maximalIdeal ψ hψs]
  ext a
  have h1 : a - ι (φ a) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa using (RingHom.congr_fun hφ (φ a)).symm
  rw [hker, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]
  simpa using (RingHom.congr_fun hψ (φ a)).symm

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom Hom.stalkMap_congr_point_assoc Hom.stalkMap_congr_hom Hom.stalkMap_comp stalkClosedPointTo Modules Opens residue Hom.stalkMap_id Pullback.exists_preimage_pullback Hom.comp_apply Modules.IsInvertible Modules.isInvertible_unit Modules.rigidify" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.ext_of_section_base_eq {κ : Type u} [Field κ] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of κ)) (p q : Spec (.of κ) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (h : p (closedPoint κ) = q (closedPoint κ)) : p = q := by

  have hpt : ∀ y : Spec (.of κ), y = closedPoint κ := fun y => Subsingleton.elim _ _

  have key : ∀ (r : Spec (.of κ) ⟶ X) (_ : r ≫ f = 𝟙 _),
      f.stalkMap (r (closedPoint κ)) ≫ r.stalkMap (closedPoint κ) =
        ((Spec (.of κ)).presheaf.stalkCongr (.of_eq (hpt (f (r (closedPoint κ)))))).hom := by
    intro r hr
    have := Scheme.Hom.stalkMap_congr_hom _ _ hr (closedPoint κ)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_id] at this

    erw [Category.comp_id] at this
    exact this

  let ι : CommRingCat.of κ ⟶ X.presheaf.stalk (p (closedPoint κ)) :=
    (stalkClosedPointIso (.of κ)).inv ≫
      ((Spec (.of κ)).presheaf.stalkCongr (.of_eq (hpt (f (p (closedPoint κ)))).symm)).hom ≫
        f.stalkMap (p (closedPoint κ))
  have h1 : ι ≫ Scheme.stalkClosedPointTo p = 𝟙 _ := by
    simp only [ι, Scheme.stalkClosedPointTo, Category.assoc]
    rw [reassoc_of% (key p hp)]
    simp
  have h2 : ι ≫ ((X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo q) = 𝟙 _ := by
    simp only [ι, Scheme.stalkClosedPointTo, Category.assoc]
    rw [Scheme.Hom.stalkMap_congr_point_assoc f _ _ h, reassoc_of% (key q hq)]
    simp

  apply (SpecToEquivOfLocalRing X (.of κ)).injective
  refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨h, ?_⟩
  change Scheme.stalkClosedPointTo p =
    (X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo q
  refine CommRingCat.hom_ext ?_
  refine RingHom.eq_of_isLocalRing_of_comp_eq_id (K := κ) _ _ ι.hom ?_ ?_
  · rw [← CommRingCat.hom_comp, h1, CommRingCat.hom_id]
  · rw [← CommRingCat.hom_comp, h2, CommRingCat.hom_id]

end AlgebraicGeometry

end PTEXT

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    {n : ℕ} (s : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
    (hsm : ∀ i, Set.range (s i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p))) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    haveI : IsProper (toBase N₀ p) := 𝔓.isProper
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (c : Fin n → Fin 2)

      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ)))
      (_hy₁ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (s i).1)
      (_hy₂ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)

      (_hc : ∀ i, Set.range (y i).base ⊆
        Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (c i)).base)

      (pos neg : Fin n → ℕ)
      (_hdeg : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0)

      (ψred : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Spec.map (CommRingCat.ofHom ρ)))
      (_ : ψred.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))),
      IsAlgEquivZero (pullback.snd (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 _))
        ((Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).obj
          ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).obj
            (Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
            (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))) := by
  intro c y hy₁ hy₂ hc pos neg hdeg ψred hψred
  classical
  haveI := 𝔓.flat
  haveI := 𝔓.lfp
  haveI : IsProper (toBase N₀ p) := 𝔓.isProper
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

  haveI hp0 : IsProper (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) :=
    𝔓.isProper_fibre0 _
  haveI hs0 : SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 _
  haveI : IsIntegral (fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))) := 𝔓.isIntegral_fibre0 _
  haveI hgi0 : GeometricallyIntegral (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) :=
    AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
  haveI := 𝔓.comp_isClosedImmersion (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0
  haveI := 𝔓.comp_isClosedImmersion (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1
  have hred := 𝔓.fibre_reduced (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))
  have hcr := 𝔓.crossing_reduced (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))
  haveI : Finite ↥(pullback (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
      (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)) := 𝔓.finite_crossings _
  haveI : IsSeparated (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) := by
    haveI := 𝔓.isProper_fibre (algebraMap (R p) (ResidueField ↥A)); infer_instance
  let i₁ : SchemeHomOver (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) :=
    ⟨𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0, 𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0⟩
  let i₂ : SchemeHomOver (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) :=
    ⟨𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1, 𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1⟩

  set pε := (DRLevel.sectionFibre 𝔓.εinf (algebraMap (R p) (ResidueField ↥A))).base
    (IsLocalRing.closedPoint (ResidueField ↥A)) with hpεdef
  have hpε1 : pε ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base :=
    𝔓.εinf_mem_comp0 _ _ ⟨IsLocalRing.closedPoint _, by rw [hpεdef]⟩
  have hpεU : pε ∈ ((pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))) ⁻¹ᵁ 𝔓.smoothLocus :
      (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).Opens) : Set _) := by
    show (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).base pε ∈ (𝔓.smoothLocus : Set _)
    apply 𝔓.εinf_mem_smoothLocus
    refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))).base (IsLocalRing.closedPoint _), ?_⟩
    rw [hpεdef, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, DRLevel.sectionFibre_fst]
  haveI : Smooth (𝔓.smoothLocus.ι ≫ toBase N₀ p) := by
    haveI := 𝔓.smoothLocus_relDim
    infer_instance
  let wb : ↥(fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))) → ↥(fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))) :=
    (DRLevel.fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) (ResidueField ↥A))).base
  have hr1 : Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base =
      wb '' Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp_w (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))]; rfl :
        (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base a =
          wb ((𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base a)))
  have hr0 : Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base =
      wb '' Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun a =>
      (by rw [← 𝔓.comp1_fibreMap_w (algebraMap (R p) (ResidueField ↥A))]; rfl :
        (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base a =
          wb ((𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base a)))
  have hne₁ : ¬ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base ⊆
      Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base := fun h =>
    𝔓.range_comp_ne _ _ (Set.Subset.antisymm h (by rw [hr1]; nth_rw 2 [hr0]; exact Set.image_mono h))
  have hne₂ : ¬ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base ⊆
      Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base := fun h =>
    𝔓.range_comp_ne _ _ (Set.Subset.antisymm (by rw [hr0]; nth_rw 2 [hr1]; exact Set.image_mono h) h)
  obtain ⟨hU, -, -, -, -⟩ :=
    AlgebraicGeometry.RelPicard.preimage_smoothLocus_eq_compl_range_and_openImmersion_of_twoGluedSmoothCurves
      (toBase N₀ p) 𝔓.smoothLocus 𝔓.smoothLocus_maximal (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))) hred
      (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))
      (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))
      i₁ i₂ (𝔓.comp_jointly_surjective _ _) hne₁ hne₂ pε hpε1 hpεU
  have hn : 0 < Nat.card ↥(pullback (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
      (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)) := by
    haveI : Nonempty ↥(pullback (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)) := by
      obtain ⟨P, hP⟩ := ModularCurve.ssPlaces_nonempty p N₀ hpN₀ (ResidueField ↥A)
      exact ⟨(𝔓.nodeEquiv _ _).symm ⟨P, hP⟩⟩
    exact Nat.card_pos

  have SEC : ∀ {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of (ResidueField ↥A))) [IsSeparated g]
      (t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Y),
      t ≫ g = 𝟙 _ → t.base (IsLocalRing.closedPoint _) ∈ closedPoints Y := by
    intro Y g _ t ht
    haveI : IsClosedImmersion (t ≫ g) := by rw [ht]; infer_instance
    haveI : IsClosedImmersion t := IsClosedImmersion.of_comp t g
    rw [mem_closedPoints_iff]
    have hr : Set.range t.base = {t.base (IsLocalRing.closedPoint _)} := by
      ext x
      constructor
      · rintro ⟨pt, rfl⟩
        rw [Set.mem_singleton_iff, show pt = IsLocalRing.closedPoint _ from Subsingleton.elim _ _]
      · rintro rfl; exact ⟨_, rfl⟩
    rw [← hr]
    exact t.isClosedEmbedding.isClosed_range

  have hyU : ∀ i, (y i).base (IsLocalRing.closedPoint _) ∈
      ((pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))) ⁻¹ᵁ 𝔓.smoothLocus :
        (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).Opens) : Set _) := by
    intro i
    show (pullback.fst (toBase N₀ p) _).base ((y i).base _) ∈ (𝔓.smoothLocus : Set _)
    rw [← Scheme.Hom.comp_apply, hy₁ i, Scheme.Hom.comp_apply]
    exact hsm i ⟨_, rfl⟩
  have hnot : ∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉
      Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base := by
    intro i hmem
    have hci := hc i ⟨IsLocalRing.closedPoint _, rfl⟩

    have hboth : (y i).base (IsLocalRing.closedPoint _) ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base ∧
        (y i).base (IsLocalRing.closedPoint _) ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base := by
      rcases (by decide : ∀ j : Fin 2, j = 0 ∨ j = 1) (c i) with hj | hj
      · rw [hj] at hci hmem
        rw [sub_zero] at hmem
        exact ⟨hci, hmem⟩
      · rw [hj] at hci hmem
        rw [sub_self] at hmem
        exact ⟨hmem, hci⟩
    obtain ⟨a, ha⟩ := hboth.1
    obtain ⟨b, hb⟩ := hboth.2
    obtain ⟨zc, hzc, -⟩ := Scheme.Pullback.exists_preimage_pullback a b (ha.trans hb.symm)
    have hpc : (y i).base (IsLocalRing.closedPoint _) ∈ Set.range (pullback.fst (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base :=
      ⟨zc, by rw [Scheme.Hom.comp_apply, hzc, ha]⟩
    have hu := hyU i
    rw [hU] at hu
    exact hu hpc

  haveI : LocallyOfFiniteType (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) :=
    inferInstance
  have hzex : ∀ i, ∃ zi : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)),
      zi ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _ ∧
      zi ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i := by
    intro i
    obtain ⟨w, hw⟩ := hc i ⟨IsLocalRing.closedPoint _, rfl⟩

    have hycl : (y i).base (IsLocalRing.closedPoint _) ∈ closedPoints (fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))) :=
      SEC _ (y i) (hy₂ i)
    haveI := 𝔓.comp_isClosedImmersion (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i)
    have hwcl : w ∈ closedPoints (fibre0 (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))) := by
      rw [mem_closedPoints_iff] at hycl ⊢
      have hpre : (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i)).base ⁻¹' {(y i).base (IsLocalRing.closedPoint _)} = {w} := by
        ext v; simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hv; exact (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i)).isClosedEmbedding.injective (hv.trans hw.symm)
        · rintro rfl; exact hw
      rw [← hpre]
      exact hycl.preimage (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i)).base.hom.continuous
    let zq := (pointEquivClosedPoint (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))).symm ⟨w, hwcl⟩
    have hzq : zq.1.base (IsLocalRing.closedPoint _) = w := by
      have e := pointEquivClosedPoint_apply_coe (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))) zq
      rw [Equiv.apply_symm_apply] at e
      exact e.symm
    refine ⟨zq.1, zq.2, ?_⟩
    refine AlgebraicGeometry.Scheme.ext_of_section_base_eq (pullback.snd _ _) _ _ ?_ (hy₂ i) ?_
    · rw [Category.assoc, 𝔓.comp_over]; exact zq.2
    · show (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i)).base (zq.1.base (IsLocalRing.closedPoint _)) = _
      rw [hzq]
      exact hw
  choose z hz hzy using hzex

  have hMinv := ModularCurve.DRModelPackageLevel.isInvertible_sectionTwist N₀ p hpN₀ 𝔓 A hA ρ hρ s hsm pos neg
  have hMR := (RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) _ hMinv).isInvertible
  have hL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).obj
          ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).obj
            (Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
            (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) ((List.finRange n).foldr
            (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (toBase N₀ p) (s i).1 (s i).2).I ^ (neg i)).module ⊗ M)
            (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules))))) := (hMR.pullback _).pullback _

  obtain ⟨e0⟩ := ModularCurve.DRModelPackageLevel.nonempty_pullbackCurve_comp0_sectionTwist_iso N₀ p hpN₀ 𝔓 A hA ρ hρ
    s hsm c y hy₁ hy₂ z hz hzy hnot ψred hψred pos neg
  have hS0 := AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
    (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) z hz (fun i => c i = 0) pos neg (hdeg 0)
  have h₁ := hS0.of_iso e0.symm

  let ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p) :=
    ⟨𝔓.εinf.1 ≫ 𝔓.π.1, by rw [Category.assoc, 𝔓.π.2, 𝔓.εinf.2]⟩
  obtain ⟨e1⟩ := ModularCurve.DRModelPackageLevel.nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso N₀ p hpN₀ 𝔓 A hA ρ hρ
    ε₀ s hsm c y hy₁ hy₂ z hz hzy hnot ψred hψred pos neg
  have hS1 := AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
    (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) z hz (fun i => c i = 1) pos neg (hdeg 1)
  have hI : ∀ i, (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I.IsInvertible :=
    fun i => RelEffCartierDiv.isInvertible_I _
  have hN1 : ∀ l : List (Fin n), Scheme.Modules.IsInvertible
      (l.foldr
        (fun i M => if c i = 1 then
          ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
          else M)
        (𝟙_ _)) := by
    intro l
    induction l with
    | nil => exact Scheme.Modules.isInvertible_unit _
    | cons i l ih =>
      rw [List.foldr_cons]
      by_cases hci : c i = 1
      · rw [if_pos hci]
        exact ((hI i).pow (pos i)).isInvertible_invModule.tensor (((hI i).pow (neg i)).isInvertible_module.tensor ih)
      · rw [if_neg hci]; exact ih
  obtain ⟨f1⟩ := AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field
    (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _) (hN1 (List.finRange n))
  obtain ⟨f2⟩ := AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field
    (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)
    (hL.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)
      (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝟙 _)))
  have h₂ := ((hS1.of_iso f1.symm).of_iso e1.symm).of_iso f2

  exact AlgebraicGeometry.RelPicard.isAlgEquivZero_of_isAlgEquivZero_pullback_curveChange_of_twoGluedSmoothCurves
    (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) hred
    (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))
    (pullback.snd (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))))
    i₁ i₂ (𝔓.comp_jointly_surjective _ _) hcr _ rfl hn (ResidueField ↥A) (𝟙 _) _ hL h₁ h₂

end S_ModularCurve_DRModelPackageLevel_isAlgEquivZero_baseChange_rigidify_sectionTwist_residueField
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isAlgEquivZero_baseChange_rigidify_sectionTwist_residueField (solution)
