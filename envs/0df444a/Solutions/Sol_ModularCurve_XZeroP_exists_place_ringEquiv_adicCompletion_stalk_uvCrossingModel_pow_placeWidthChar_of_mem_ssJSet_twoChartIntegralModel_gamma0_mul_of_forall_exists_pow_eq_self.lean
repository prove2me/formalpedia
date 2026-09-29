-- Prove2me | solution 1 for ModularCurve.XZeroP.exists_place_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_placeWidthChar_of_mem_ssJSet_twoChartIntegralModel_gamma0_mul_of_forall_exists_pow_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f504022a-00bf-521b-8457-21f95f5c6f60

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AdicCompletionRingFunctoriality
import Theorems.Thm_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
import Theorems.Thm_ModularCurve_exists_placeSpecialization_prolongationTuple_isModel_regularityLaw_nodeValueLaw_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed
import Theorems.Thm_ModularCurve_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_ModularCurve_XZeroP_exists_mem_ssPlaces_ringHom_eq_residueFst_of_mem_ssJSet_chartAlgFin_twoChartIntegralModel_gamma0_mul
import Theorems.Thm_ValuationSubring_forall_exists_pow_prime_pow_eq_self_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace
import Theorems.Thm_ModularCurve_XZeroP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
import Theorems.Thm_ModularCurve_CharPModel_exists_fibreModel_cuspChart_placeSpecialization_sp_eq_spPlace_of_one_lt
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed_of_liesOverPrime
import Theorems.Thm_ModularCurve_XZeroP_exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_exists_place_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_placeWidthChar_of_mem_ssJSet_twoChartIntegralModel_gamma0_mul_of_forall_exists_pow_eq_self
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries'"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure"
p2m_attr_erase "instance" "instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal"
p2m_attr_erase "instance" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.symPoly_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one"
p2m_attr_erase "simp" "AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply"
p2m_attr_erase "simp" "ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.crossingCoord_apply ModularCurve.coe_baseChangeRingHom AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace B8

theorem exists_ringEquiv_localization_of_forall_mem_iff
    {A₂ : Type*} [CommRing A₂] [IsDomain A₂] (𝔶₂ : Ideal A₂) [𝔶₂.IsPrime]
    (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (ι : A₂ →+* ↥F) (hι : Function.Injective ι)
    (Nd : Subring ↥F)
    (hmem : ∀ g : ↥F, g ∈ Nd ↔ ∃ c s : A₂, s ∉ 𝔶₂ ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) * ((ι s : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((ι c : ↥F) : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ β : Localization.AtPrime 𝔶₂ ≃+* ↥Nd,
      ∀ (b : A₂) (t : 𝔶₂.primeCompl),
        ((β (IsLocalization.mk' (Localization.AtPrime 𝔶₂) b t) : ↥Nd) : ↥F) * ι t = ι b := by
  classical

  have hunit : ∀ t : 𝔶₂.primeCompl, IsUnit (ι t) := fun t => by
    rw [isUnit_iff_ne_zero]
    intro h0
    have : (t : A₂) = 0 := hι (by rw [h0, map_zero])
    exact t.2 (this ▸ 𝔶₂.zero_mem)
  let β₀ : Localization.AtPrime 𝔶₂ →+* ↥F := IsLocalization.lift (M := 𝔶₂.primeCompl) hunit
  have hβ₀mk : ∀ (b : A₂) (t : 𝔶₂.primeCompl), β₀ (IsLocalization.mk' _ b t) * ι t = ι b := fun b t => by
    have h := (IsLocalization.lift_mk'_spec (M := 𝔶₂.primeCompl) hunit b (β₀ (IsLocalization.mk' _ b t)) t).mp rfl

    rw [h, mul_comm]

  have hβ₀inj : Function.Injective β₀ := by
    intro z₁ z₂ h
    obtain ⟨⟨b₁, t₁⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔶₂.primeCompl z₁
    obtain ⟨⟨b₂, t₂⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔶₂.primeCompl z₂
    rw [IsLocalization.mk'_eq_iff_eq]
    congr 1
    apply hι
    rw [map_mul, map_mul]
    have h1 := hβ₀mk b₁ t₁
    have h2 := hβ₀mk b₂ t₂

    calc ι t₂ * ι b₁ = ι t₂ * (β₀ (IsLocalization.mk' _ b₁ t₁) * ι t₁) := by rw [h1]
      _ = ι t₁ * (β₀ (IsLocalization.mk' _ b₂ t₂) * ι t₂) := by rw [h]; ring
      _ = ι t₁ * ι b₂ := by rw [h2]

  have hrange : β₀.range = Nd := by
    ext g
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔶₂.primeCompl z
      refine (hmem _).mpr ⟨b, t, t.2, ?_⟩
      rw [← Subring.coe_mul F.toSubring]
      · show ((β₀ (IsLocalization.mk' _ b t) * ι t : ↥F) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [hβ₀mk]
    · intro hg
      obtain ⟨c, s, hs, hcs⟩ := (hmem g).mp hg
      refine ⟨IsLocalization.mk' _ c (⟨s, hs⟩ : 𝔶₂.primeCompl), ?_⟩
      have hιs : (ι s : ↥F) ≠ 0 := (hunit ⟨s, hs⟩).ne_zero
      have hg' : g = ι c * (ι s)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hιs]
        apply Subtype.val_injective
        exact hcs
      have hb : β₀ (IsLocalization.mk' _ c (⟨s, hs⟩ : 𝔶₂.primeCompl)) = ι c * (ι s)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hιs]
        exact hβ₀mk c ⟨s, hs⟩
      rw [hb, hg']
  refine ⟨(RingEquiv.ofBijective β₀.rangeRestrict ⟨fun a b h => hβ₀inj (congrArg Subtype.val h),
      β₀.rangeRestrict_surjective⟩).trans (RingEquiv.subringCongr hrange), fun b t => ?_⟩
  show (β₀ (IsLocalization.mk' _ b t) : ↥F) * ι t = ι b
  exact hβ₀mk b t

theorem exists_adicCompletion_ringEquiv_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    ∃ P : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, P (algebraMap R _ r) = algebraMap S _ (e r) := by
  let eA : R ≃ₐ[ℤ] S := AlgEquiv.ofRingEquiv (f := e) (fun n => by simp)
  have hmap : (IsLocalRing.maximalIdeal R).map (eA : R →ₐ[ℤ] S) ≤ IsLocalRing.maximalIdeal S := by
    refine IsLocalRing.le_maximalIdeal (fun htop => ?_)
    have h1 : (1 : S) ∈ (IsLocalRing.maximalIdeal R).map (eA : R →ₐ[ℤ] S) := htop ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective (eA : R →ₐ[ℤ] S) eA.surjective).mp h1
    apply (IsLocalRing.mem_maximalIdeal _).mp hx
    have : eA x = eA 1 := by rw [map_one]; exact hx1
    rw [eA.injective this]
    exact isUnit_one
  have hmap' : (IsLocalRing.maximalIdeal S).map (eA.symm : S →ₐ[ℤ] R) ≤ IsLocalRing.maximalIdeal R := by
    refine IsLocalRing.le_maximalIdeal (fun htop => ?_)
    have h1 : (1 : R) ∈ (IsLocalRing.maximalIdeal S).map (eA.symm : S →ₐ[ℤ] R) := htop ▸ Submodule.mem_top
    obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective (eA.symm : S →ₐ[ℤ] R) eA.symm.surjective).mp h1
    apply (IsLocalRing.mem_maximalIdeal _).mp hx
    have : eA.symm x = eA.symm 1 := by rw [map_one]; exact hx1
    rw [eA.symm.injective this]
    exact isUnit_one
  refine ⟨(AdicCompletion.mapAlgEquiv (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) eA hmap hmap').toRingEquiv,
    fun r => ?_⟩
  show AdicCompletion.mapAlgEquiv _ _ eA _ _ (algebraMap R _ r) = _
  rw [AdicCompletion.mapAlgEquiv_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.mapₐ_of, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

theorem residual_transport {S T W : Type*} [CommRing S] [CommRing T] [CommRing W] [IsLocalRing S] [IsLocalRing T]
    (θ : S ≃+* T)
    (Θ : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* AdicCompletion (IsLocalRing.maximalIdeal T) T)
    (hΘ : ∀ s : S, Θ (algebraMap S _ s) = algebraMap T _ (θ s))
    (σ₂ : W →+* AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (hres : ∀ f : S, ∃ o : W, algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) f - σ₂ o ∈
      Ideal.map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (IsLocalRing.maximalIdeal S)) :
    ∀ g : T, ∃ o : W, algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T) g - (Θ.toRingHom.comp σ₂) o ∈
      Ideal.map (algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T)) (IsLocalRing.maximalIdeal T) := by
  intro g
  obtain ⟨o, ho⟩ := hres (θ.symm g)
  refine ⟨o, ?_⟩
  have hmapΘ : Ideal.map (Θ.toRingHom.comp (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)))
      (IsLocalRing.maximalIdeal S) ≤
      Ideal.map (algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T)) (IsLocalRing.maximalIdeal T) := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hΘ]
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu => hs (by simpa using hu.map θ.symm)
  have hx := Ideal.mem_map_of_mem (Θ.toRingHom) ho
  rw [map_sub, Ideal.map_map] at hx
  have h1 : Θ.toRingHom (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (θ.symm g)) =
      algebraMap T (AdicCompletion (IsLocalRing.maximalIdeal T) T) g := by
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hΘ, RingEquiv.apply_symm_apply]
  rw [h1] at hx
  exact hmapΘ hx

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem tail
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    {A : Type} [CommRing A] (ϖ : A)
    {Ab : ValuationSubring (AlgebraicClosure ℚ)} (hAb : Ab.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Ab) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Ab)] [DecidableEq (IsLocalRing.ResidueField ↥Ab)]
    {data : ModularCurve.ModularPolynomialData p} {hKr : ModularCurve.KroneckerCongruence p data}
    {hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M p}
    {hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) M p}
    {P : ModularCurve.PlaceSpecialization Ab p M data hKr (IsLocalRing.ResidueField ↥Ab) (IsLocalRing.residue ↥Ab) hα hβ}
    (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (W : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Ab) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)))
    (hW : ∀ w ∈ W, w ∈ ModularCurve.ssPlaces p M (IsLocalRing.ResidueField ↥Ab))
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Ab) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)) (hw : w ∈ W)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (cA : A → ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) (ϖb : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) (hcAϖ : cA ϖ = ϖb)
    (hϖb : ∀ d : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K),
      ModularCurve.NodeLocalized.redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
    (ε : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) (hε : IsUnit ε)
    (hqe : ((p : ℕ) : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) = ϖb ^ (p - 1) * ε)
    {S : Type} [CommRing S] [IsLocalRing S] (g : A → S)
    (θ : S ≃+* ↥(R.nodeIntegersOver K w)) (hθ : ∀ a : A, θ (g a) = R.nodeConst K w (cA a))
    {W₂ : Type} [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (IsLocalRing.maximalIdeal W₂) W₂]
    (τ₂ : A →+* W₂) (hτ₂ : IsLocalRing.maximalIdeal W₂ = Ideal.span {τ₂ ϖ})
    (σ₂ : W₂ →+* AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (hσ₂τ₂ : ∀ a : A, σ₂ (τ₂ a) = algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (g a))
    (hσ₂res : ∀ f : S, ∃ o : W₂, algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) f - σ₂ o ∈
      Ideal.map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) (IsLocalRing.maximalIdeal S)) :
    ∃ e₂ : AdicCompletion (IsLocalRing.maximalIdeal S) S ≃+* ModularCurve.UVCrossingModel W₂ ((τ₂ ϖ) ^ ((p - 1) * ModularCurve.placeWidthChar p M w)),
      ∀ a : A, e₂ (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (g a)) =
        ModularCurve.UVCrossingModel.const ((τ₂ ϖ) ^ ((p - 1) * ModularCurve.placeWidthChar p M w)) (τ₂ a) := by
  classical
  obtain ⟨Θ, hΘ⟩ := B8.exists_adicCompletion_ringEquiv_of_ringEquiv θ
  have hπ : Irreducible (τ₂ ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hτ₂
  let σ : W₂ →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) :=
    Θ.toRingHom.comp σ₂
  have hσπ : σ (τ₂ ϖ) = algebraMap _ _ (R.nodeConst K w ϖb) := by
    show Θ (σ₂ (τ₂ ϖ)) = _
    rw [hσ₂τ₂, hΘ, hθ, hcAϖ]
  have hσ := B8.residual_transport θ Θ hΘ σ₂ hσ₂res
  obtain ⟨E, hE1, c, u, hu, hxy, ι, α, β', hα', hβ', hισ, hιx, hιy, -, -⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
      R hpM hmodel W hW hreg hval hord K w hw ϖb hϖb (τ₂ ϖ) hπ σ hσπ hσ
  have hE : E = (p - 1) * ModularCurve.placeWidthChar p M w := by
    have := ModularCurve.PlaceSpecialization.ProlongationTuple.crossingExponent_eq_placeWidthChar_mul_of_orderLawFixed_of_liesOverPrime
      hAb R hpM hmodel W hW hreg hval hord K w hw ϖb hϖb (p - 1) ε hε hqe c E u hu hxy
    rw [this, Nat.mul_comm]
  rw [show (p - 1) * ModularCurve.placeWidthChar p M w = E from hE.symm]
  refine ⟨Θ.trans ι, fun a => ?_⟩
  rw [RingEquiv.trans_apply, ← hσ₂τ₂]
  exact hισ (τ₂ a)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem certificate (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Ab : ValuationSubring (AlgebraicClosure ℚ)) (hAb : Ab.LiesOverPrime p) [CharP (IsLocalRing.ResidueField ↥Ab) p]
    {data : ModularCurve.ModularPolynomialData p} {hKr : ModularCurve.KroneckerCongruence p data}
    {hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M p}
    {hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) M p}
    (P : ModularCurve.PlaceSpecialization Ab p M data hKr (IsLocalRing.ResidueField ↥Ab) (IsLocalRing.residue ↥Ab) hα hβ)
    (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hord : R.OrderLawFixed) :
    ∃ (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ M → ModularCurve.ModularPolynomialData d)
      (hsep : (((dataAll M (dvd_refl M)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥Ab)))).map
        (algebraMap (Polynomial (IsLocalRing.ResidueField ↥Ab)) (RatFunc (IsLocalRing.ResidueField ↥Ab)))).Separable)
      (fm₀ : ModularCurve.CharPModel.FibreModel M Ab p (IsLocalRing.ResidueField ↥Ab) (IsLocalRing.residue ↥Ab))
      (_ : fm₀.CuspChart),
      P.sp = fm₀.spPlace Ideal.Quotient.mk_surjective dataAll hsep := by
  classical
  have dataAll : ∀ (d : ℕ) [NeZero d], d ∣ M → ModularCurve.ModularPolynomialData d :=
    fun d _ _ => Classical.choice (ModularCurve.nonempty_modularPolynomialData d)
  have hsep : (((dataAll M (dvd_refl M)).Φ.map
      (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥Ab)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥Ab)) (RatFunc (IsLocalRing.ResidueField ↥Ab)))).Separable :=
    ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero (IsLocalRing.ResidueField ↥Ab) M
      (dataAll M (dvd_refl M)) (by rw [Ne, CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥Ab) p]; exact hpM)
  obtain ⟨fm₀, hcusp, -, -⟩ :=
    ModularCurve.CharPModel.exists_fibreModel_cuspChart_placeSpecialization_sp_eq_spPlace_of_one_lt
      M (by omega) p hpM Ab hAb data hKr hα hβ dataAll hsep
  exact ⟨dataAll, hsep, fm₀, hcusp,
    ModularCurve.PlaceSpecialization.sp_eq_spPlace_of_isModel_of_orderLawFixed R hpM hmodel hord fm₀ hcusp
      Ideal.Quotient.mk_surjective dataAll hsep⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem bridgeGlue
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K₂ : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) [Fact (j₂ ≠ 0)]
    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂)) [𝔶₂.IsMaximal]
    (e : L →+* AlgebraicClosure ℚ) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (Ab : ValuationSubring (AlgebraicClosure ℚ)) (hAb : Ab.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Ab) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Ab)] [DecidableEq (IsLocalRing.ResidueField ↥Ab)]
    (hcoeff : ∀ x : AlgebraicClosure ℚ, x ∈ ModularCurve.NodeLocalized.coeffSubring Ab K ↔ ∃ a : A, x = e (algebraMap A L a))
    (Ψ : ↥(chartAlgFin A (↥K₂) j₂) ≃+* ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K))
    (hΨ : ∀ b : ↥(chartAlgFin A (↥K₂) j₂),
      ((Ψ b : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L))
    {data : ModularCurve.ModularPolynomialData p} {hKr : ModularCurve.KroneckerCongruence p data}
    {hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M p}
    {hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) M p}
    (P : ModularCurve.PlaceSpecialization Ab p M data hKr (IsLocalRing.ResidueField ↥Ab) (IsLocalRing.residue ↥Ab) hα hβ)
    (R : ModularCurve.PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hord : R.OrderLawFixed)
    (w : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Ab) ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M))
    (hw : w ∈ ModularCurve.ssPlaces p M (IsLocalRing.ResidueField ↥Ab))
    (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M))
    (hρpin : ∀ b : ↥(chartAlgFin A (↥K₂) j₂), ∃ (f : ↥(ModularCurve.modularFunctionFieldBar (M * p))) (hf : f ∈ R.R₁.integers),
      ((f : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ))
          = ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L) ∧
        ρ b = R.residue₁ ⟨f, hf⟩)
    (hρint : ∀ b, ρ b ∈ w.toValuationSubring)
    (hρcent : ∀ b, ρ b ∈ w.toValuationSubring.nonunits ↔ b ∈ 𝔶₂)

    (𝔪 : Ideal ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) [𝔪.IsMaximal]
    (hmemN : ∀ g : ↥(ModularCurve.modularFunctionFieldBar (M * p)), g ∈ R.nodeIntegersOver K w ↔
      ∃ r s : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K), s ∉ 𝔪 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = (r : LaurentSeries (AlgebraicClosure ℚ)))

    (V : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar (M * p)))
    (hV : P.reduceFst V = w) :
    ∃ β : Localization.AtPrime 𝔶₂ ≃+* ↥(R.nodeIntegersOver K w),
      ∀ a : A, β (algebraMap A (Localization.AtPrime 𝔶₂) a) =
        R.nodeConst K w ⟨e (algebraMap A L a), (hcoeff _).mpr ⟨a, rfl⟩⟩ := by
  classical

  have hmemF : ∀ b : ↥(chartAlgFin A (↥K₂) j₂),
      ((Ψ b : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ ModularCurve.modularFunctionFieldBar (M * p) := fun b => by
    obtain ⟨f, -, hfe, -⟩ := hρpin b
    rw [hΨ, ← hfe]
    exact f.2
  let ι : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldBar (M * p)) :=
    { toFun := fun b => ⟨_, hmemF b⟩
      map_one' := Subtype.ext (show ((Ψ 1 : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) = _ by
        rw [map_one, OneMemClass.coe_one, OneMemClass.coe_one])
      map_mul' := fun x y => Subtype.ext (show ((Ψ (x * y) : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) = _ by
        rw [map_mul, MulMemClass.coe_mul, MulMemClass.coe_mul])
      map_zero' := Subtype.ext (show ((Ψ 0 : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) = _ by
        rw [map_zero, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero])
      map_add' := fun x y => Subtype.ext (show ((Ψ (x + y) : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) = _ by
        rw [map_add, AddMemClass.coe_add, AddMemClass.coe_add]) }
  have hιcoe : ∀ b, ((ι b : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
      ((Ψ b : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) := fun b => rfl
  have hι : Function.Injective ι := fun x y h => by
    apply Ψ.injective
    apply Subtype.ext
    rw [← hιcoe, ← hιcoe, h]

  have hιR₁ : ∀ b, (ι b) ∈ R.R₁.integers ∧ ∃ h : ι b ∈ R.R₁.integers, ρ b = R.residue₁ ⟨ι b, h⟩ := fun b => by
    obtain ⟨f, hf, hfe, hρ⟩ := hρpin b
    have hfι : f = ι b := Subtype.ext (by rw [hfe, hιcoe, hΨ])
    subst hfι
    exact ⟨hf, hf, hρ⟩

  obtain ⟨dataAll, hsep, fm₀, hcusp, hP⟩ := B8.certificate p M hM hpM Ab hAb P R hmodel hord
  obtain ⟨K₁', _fd1, hKK₁, hcef⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.hasValue_nodeResidue_red_of_hasValue_of_mem_nodeIntegersOver_of_sp_eq_spPlace
      hpM fm₀ Ideal.Quotient.mk_surjective dataAll hsep P hP R w hw K inferInstance
  obtain ⟨K₂', _fd2, hKK₂, h9ee⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_iff_hasValue_residueFst_zero_jIntegralClosure_of_sp_eq_spPlace
      hpM fm₀ Ideal.Quotient.mk_surjective dataAll hsep P hP R w hw K inferInstance
  haveI := _fd1
  haveI := _fd2
  let K' : IntermediateField ℚ (AlgebraicClosure ℚ) := K₁' ⊔ K₂'
  haveI : FiniteDimensional ℚ ↥K' := IntermediateField.finiteDimensional_sup K₁' K₂'
  have hKK' : K ≤ K' := hKK₁.trans le_sup_left
  have hcefK := hcef K' inferInstance le_sup_left V hV
  have h9eeK := h9ee K' inferInstance le_sup_right V hV

  have hfieldmono : ∀ x, x ∈ ModularCurve.NodeLocalized.fieldOver (M * p) K → x ∈ ModularCurve.NodeLocalized.fieldOver (M * p) K' := by
    intro x hx
    refine Subfield.closure_mono ?_ hx
    apply Set.union_subset_union_left
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨(c : AlgebraicClosure ℚ), hKK' c.2⟩, rfl⟩
  have hjRmono : ModularCurve.NodeLocalized.jRing Ab K ≤ ModularCurve.NodeLocalized.jRing Ab K' := by
    refine Subring.closure_mono ?_
    apply Set.union_subset_union_left
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨(c : AlgebraicClosure ℚ), c.2.1, hKK' c.2.2⟩, rfl⟩
  have hjICmono : ∀ x, x ∈ ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K →
      x ∈ ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K' := by
    rintro x ⟨hxF, q, hq, hq0⟩
    refine ⟨hfieldmono x hxF, q.map (Subring.inclusion hjRmono), hq.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hq0
  have monoN : ∀ g : ↥(ModularCurve.modularFunctionFieldBar (M * p)), g ∈ R.nodeIntegersOver K w → g ∈ R.nodeIntegersOver K' w :=
    fun g hg => ⟨hg.1, hfieldmono _ hg.2⟩
  have memV : ∀ g : ↥(ModularCurve.modularFunctionFieldBar (M * p)), g ∈ R.nodeIntegersOver K' w →
      (g : ↥(ModularCurve.modularFunctionFieldBar (M * p))) ∈ V.toValuationSubring := fun g hg => hg.1.2.2 V hV
  have h1𝔪 : (1 : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) ∉ 𝔪 :=
    (Ideal.ne_top_iff_one 𝔪).mp (Ideal.IsMaximal.ne_top ‹_›)
  have hιN : ∀ b, ι b ∈ R.nodeIntegersOver K w := fun b =>
    (hmemN _).mpr ⟨Ψ b, 1, h1𝔪, by rw [OneMemClass.coe_one, mul_one, hιcoe]⟩

  have hsub : ∀ b : ↥(chartAlgFin A (↥K₂) j₂), b ∈ 𝔶₂ → Ψ b ∈ 𝔪 := by
    intro b hb
    by_contra hΨb
    have hιb0 : ι b ≠ 0 := by
      intro h0
      apply hΨb
      have : b = 0 := hι (by rw [h0, map_zero])
      rw [this, map_zero]
      exact 𝔪.zero_mem

    have hg : (ι b)⁻¹ ∈ R.nodeIntegersOver K w := (hmemN _).mpr ⟨1, Ψ b, hΨb, by
      rw [OneMemClass.coe_one, ← hιcoe, ← MulMemClass.coe_mul, inv_mul_cancel₀ hιb0, OneMemClass.coe_one]⟩
    have hgV := memV _ (monoN _ hg)
    have hιbV := memV _ (monoN _ (hιN b))

    obtain ⟨hιb₁, hιb₁', hρb⟩ := hιR₁ b
    have hw₀ : w.HasValue (ρ b) 0 := by
      refine ⟨hρint b, ?_⟩
      rw [map_zero, IsLocalRing.residue_eq_zero_iff]
      obtain ⟨h', hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp ((hρcent b).mpr hb)
      exact hm

    obtain ⟨a, haV, hiff⟩ := h9eeK (ι b) (hjICmono _ (by rw [hιcoe]; exact (Ψ b).2))
    have ha𝔪 : a ∈ IsLocalRing.maximalIdeal ↥Ab := hiff.mp ⟨hιb₁', hρb ▸ hw₀⟩

    have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      have hres := haV.2
      rw [h0, map_zero, IsLocalRing.residue_eq_zero_iff] at hres
      apply (IsLocalRing.mem_maximalIdeal _).mp hres
      exact IsUnit.of_mul_eq_one ⟨_, hgV⟩ (Subtype.ext (mul_inv_cancel₀ hιb0))
    have hgval := haV.inv ha0

    obtain ⟨hainvA, -, -⟩ := hcefK ⟨_, monoN _ hg⟩ (a : AlgebraicClosure ℚ)⁻¹ hgval
    apply (IsLocalRing.mem_maximalIdeal _).mp ha𝔪
    exact IsUnit.of_mul_eq_one ⟨_, hainvA⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
  have h𝔶𝔪 : ∀ b : ↥(chartAlgFin A (↥K₂) j₂), b ∈ 𝔶₂ ↔ Ψ b ∈ 𝔪 := by
    have heq : 𝔶₂ = 𝔪.comap Ψ.toRingHom :=
      Ideal.IsMaximal.eq_of_le ‹𝔶₂.IsMaximal› (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)) (fun b hb => hsub b hb)
    intro b
    rw [heq]
    rfl

  have hmem' : ∀ g : ↥(ModularCurve.modularFunctionFieldBar (M * p)), g ∈ R.nodeIntegersOver K w ↔
      ∃ c s : ↥(chartAlgFin A (↥K₂) j₂), s ∉ 𝔶₂ ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * ((ι s : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((ι c : ↥(ModularCurve.modularFunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro g
    rw [hmemN]
    constructor
    · rintro ⟨r, s, hs, h⟩
      refine ⟨Ψ.symm r, Ψ.symm s, fun h' => hs ?_, ?_⟩
      · rw [h𝔶𝔪, RingEquiv.apply_symm_apply] at h'
        exact h'
      · rw [hιcoe, hιcoe, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        exact h
    · rintro ⟨c, s, hs, h⟩
      exact ⟨Ψ c, Ψ s, fun h' => hs ((h𝔶𝔪 s).mpr h'), by rw [← hιcoe, ← hιcoe]; exact h⟩
  haveI : 𝔶₂.IsPrime := Ideal.IsMaximal.isPrime ‹_›
  obtain ⟨β, hβ⟩ := B8.exists_ringEquiv_localization_of_forall_mem_iff 𝔶₂ (ModularCurve.modularFunctionFieldBar (M * p)) ι hι
    (R.nodeIntegersOver K w) hmem'
  refine ⟨β, fun a => ?_⟩
  apply Subtype.ext
  have h1 := hβ (algebraMap A _ a) 1
  rw [OneMemClass.coe_one, map_one, mul_one, IsLocalization.mk'_one] at h1
  rw [IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K₂) j₂) (Localization.AtPrime 𝔶₂), h1,
    ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst]
  apply Subtype.ext
  rw [hιcoe, hΨ]
  change ModularCurve.coeffMap e (((algebraMap A ↥(chartAlgFin A (↥K₂) j₂) a : ↥(chartAlgFin A (↥K₂) j₂)) : ↥K₂) : LaurentSeries L) =
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (e (algebraMap A L a))
  rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K₂]
  change ModularCurve.coeffMap e (algebraMap L (LaurentSeries L) (algebraMap A L a)) = _
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single]

end B8

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
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

    (z₂ : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂))
    (ϖz₂ : (AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)
    (hϖz₂ : ϖz₂ = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ z₂ trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz₂ : ϖz₂ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))
    (y₂ : ↥(XFin A (↥K₂) j₂)) (hy₂ : (ιFin A (↥K₂) j₂).base y₂ = z₂)
    (hss₂ : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₂) j₂) →+* Ω),
      RingHom.ker φ = y₂.asIdeal → φ (jChartFin A (↥K₂) j₂) ∈ ModularCurve.ssJSet p Ω)

    (𝔶₂ : Ideal ↥(chartAlgFin A (↥K₂) j₂)) (h𝔶₂ : 𝔶₂ = y₂.asIdeal) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (_ : IsAlgClosed k) (_ : DecidableEq k)
      (_ : ∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x)
      (w : AlgebraicCurve.Place k ↥(ModularCurve.modularFunctionFieldC k M))
      (_ : w ∈ ModularCurve.ssPlaces p M k)
      (ρ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(ModularCurve.modularFunctionFieldC k M))
      (_ : ρ (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) = 0)
      (_ : ρ (jChartFin A (↥K₂) j₂) = ModularCurve.jGeomGen k M)
      (_ : ∀ b, ρ b ∈ w.toValuationSubring)
      (_ : ∀ b, ρ b ∈ w.toValuationSubring.nonunits ↔ b ∈ 𝔶₂)
      (_ : ∀ f : ↥(ModularCurve.modularFunctionFieldC k M), ∃ a b : ↥(Algebra.adjoin k (Set.range ρ)),
        (b : ↥(ModularCurve.modularFunctionFieldC k M)) ≠ 0 ∧ f * b = a),
      ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsDiscreteValuationRing W₂)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₂) W₂) (σ₂ : A →+* W₂)
        (_ : IsLocalRing.maximalIdeal W₂ = Ideal.span {σ₂ ϖ})
        (e₂ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) ≃+*
          ModularCurve.UVCrossingModel W₂ ((σ₂ ϖ) ^ ((p - 1) * ModularCurve.placeWidthChar p M w))),
        ∀ a : A, e₂ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk z₂))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ z₂ trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          ModularCurve.UVCrossingModel.const ((σ₂ ϖ) ^ ((p - 1) * ModularCurve.placeWidthChar p M w)) (σ₂ a) := by
  classical
  subst h𝔶₂
  subst hy₂

  obtain ⟨e, K, _fdK, hKrange, Ab, hAb, hA, hbase, hcoeff, ϖb, hϖbe, hϖb, ε, hε, hqe, hfield, instK, hinstK, jK, hjK, _fjK, Φ, hΦ, Ψ, hΨ⟩ :=
    ModularCurve.XZeroP.exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
      p M hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ
  haveI := _fdK
  haveI hchar : CharP (IsLocalRing.ResidueField ↥Ab) p := ValuationSubring.charP_residueField_of_liesOverPrime_def Fact.out hAb
  letI hdec := ModularCurve.instDecidableEqResidueFieldSemistable Ab
  letI halg := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable Ab M
  haveI hac : IsAlgClosed (IsLocalRing.ResidueField ↥Ab) := ValuationSubring.isAlgClosed_residueField Ab
  obtain ⟨Wss, hWss⟩ : ∃ Wss : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Ab)
      ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥Ab) M)),
      ∀ w, w ∈ Wss ↔ w ∈ ModularCurve.ssPlaces p M (IsLocalRing.ResidueField ↥Ab) :=
    ⟨(ModularCurve.ssPlaces_finite p M (IsLocalRing.ResidueField ↥Ab)).toFinset, fun w => Set.Finite.mem_toFinset _⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  have hKr := ModularCurve.kroneckerCongruence_of_prime p data
  obtain ⟨Ptel, R, hmodel, hreg, hval, hord⟩ :=
    ModularCurve.exists_placeSpecialization_prolongationTuple_isModel_regularityLaw_nodeValueLaw_orderLawFixed M p Fact.out hpM Ab hAb
      Wss hWss data hKr (ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) M p)
      (ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) M p)
  have hWss' : ∀ v ∈ Wss, v ∈ ModularCurve.ssPlaces p M (IsLocalRing.ResidueField ↥Ab) := fun v hv => (hWss v).1 hv

  have hcoe : ∀ a : A, e (algebraMap A L a) ∈ ModularCurve.NodeLocalized.coeffSubring Ab K := fun a => (hcoeff _).mpr ⟨a, rfl⟩

  obtain ⟨δ, hδA, hδchart⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K₂) j₂ y₂ ⟨y₂, trivial, rfl⟩
  have h𝔶₂ϖ : algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ ∈ y₂.asIdeal := by
    let δe := CategoryTheory.Iso.commRingCatIsoToRingEquiv
      (S := CommRingCat.of (@Localization.AtPrime ↥(chartAlgFin A (↥K₂) j₂) _ y₂.asIdeal _)) δ
    have h1 : ¬ IsUnit (δe ϖz₂) := fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hz₂ (by have h' := hu.map δe.symm; rwa [RingEquiv.symm_apply_apply] at h')
    rw [hϖz₂] at h1
    change ¬ IsUnit (δ.hom.hom _) at h1
    rw [hδA] at h1
    have h2 : algebraMap A (@Localization.AtPrime ↥(chartAlgFin A (↥K₂) j₂) _ y₂.asIdeal _) ϖ ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr h1
    rw [IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K₂) j₂)
      (@Localization.AtPrime ↥(chartAlgFin A (↥K₂) j₂) _ y₂.asIdeal _)] at h2
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ y₂.asIdeal _).mp h2

  obtain ⟨w, hw, ρ, hρpin, hρϖ, hρj, hρint, hρcent, hρbir⟩ :=
    ModularCurve.XZeroP.exists_mem_ssPlaces_ringHom_eq_residueFst_of_mem_ssJSet_chartAlgFin_twoChartIntegralModel_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ y₂ hss₂ y₂.asIdeal rfl h𝔶₂ϖ e Ab hA hbase data hKr
      (ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) M p) (ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) M p) Ptel R
  have hwW : w ∈ Wss := (hWss w).2 hw

  obtain ⟨hloc, hnoeth, 𝔪, h𝔪max, hmemN⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
      R hpM hord Wss hWss' hreg K w hwW
  haveI := hloc
  haveI := hnoeth
  haveI := h𝔪max
  obtain ⟨V, hV⟩ := ModularCurve.PlaceSpecialization.reduceFst_surjective Ptel w
  haveI hymax : (y₂.asIdeal : Ideal ↥(chartAlgFin A (↥K₂) j₂)).IsMaximal :=
    (ModularCurve.XZeroP.isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ y₂ h𝔶₂ϖ hss₂).1
  obtain ⟨β, hβ⟩ := B8.bridgeGlue p M hM hpM L K₂ A j₂ (y₂.asIdeal : Ideal ↥(chartAlgFin A (↥K₂) j₂)) e K Ab hAb hcoeff Ψ hΨ
    Ptel R hmodel hord w hw ρ hρpin hρint hρcent 𝔪 hmemN V hV

  obtain ⟨W₂, _iW1, _iW2, _iW3, _iW4, τ₂, hτ₂, σ₂, hσ₂τ₂, hσ₂res⟩ :
      ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsDiscreteValuationRing W₂)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W₂) W₂) (τ₂ : A →+* W₂)
        (_ : IsLocalRing.maximalIdeal W₂ = Ideal.span {τ₂ ϖ})
        (σ₂ : W₂ →+* (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)))),
        (∀ a : A, σ₂ (τ₂ a) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) ((((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))))) ∧
        ∀ f : ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)), ∃ o : W₂, algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) f - σ₂ o ∈
          Ideal.map (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)) (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)))) (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂))) := by
    exact ModularCurve.XZeroP.exists_completeDVR_algebraMap_ringHom_adicCompletion_stalk_twoChartIntegralModel_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ _ ϖz₂ hϖz₂ hz₂ y₂ rfl hss₂ _ rfl

  obtain ⟨θ, hθ⟩ : ∃ θ : ((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂)) ≃+* ↥(R.nodeIntegersOver K w), ∀ a : A,
      θ ((((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) = R.nodeConst K w ⟨e (algebraMap A L a), hcoe a⟩ :=
    ⟨(CategoryTheory.Iso.commRingCatIsoToRingEquiv (S := CommRingCat.of (@Localization.AtPrime ↥(chartAlgFin A (↥K₂) j₂) _ y₂.asIdeal _)) δ).trans β, fun a => by
      rw [RingEquiv.trans_apply]
      show β (δ.hom.hom _) = _
      rw [hδA, hβ]⟩

  obtain ⟨e₂, he₂⟩ := B8.tail p M hpM ϖ hAb R hmodel Wss hWss' hreg hval hord K w hwW
    (fun a => ⟨e (algebraMap A L a), hcoe a⟩) ϖb (Subtype.ext hϖbe.symm) hϖb ε hε hqe
    (fun a : A => ((((AlgebraicCurve.TwoChartIntegralModel A (↥K₂) j₂).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K₂) j₂).base y₂) trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₂) j₂).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))))) θ hθ τ₂ hτ₂ σ₂ hσ₂τ₂ hσ₂res
  exact ⟨IsLocalRing.ResidueField ↥Ab, inferInstance, hchar, hac, hdec,
    ValuationSubring.forall_exists_pow_prime_pow_eq_self_residueField Ab p, w, hw, ρ, hρϖ, hρj, hρint, hρcent, hρbir,
    W₂, _iW1, _iW2, _iW3, _iW4, τ₂, hτ₂, e₂, he₂⟩

end S_ModularCurve_XZeroP_exists_place_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_placeWidthChar_of_mem_ssJSet_twoChartIntegralModel_gamma0_mul_of_forall_exists_pow_eq_self
end P2MW
export P2MW.S_ModularCurve_XZeroP_exists_place_ringEquiv_adicCompletion_stalk_uvCrossingModel_pow_placeWidthChar_of_mem_ssJSet_twoChartIntegralModel_gamma0_mul_of_forall_exists_pow_eq_self (solution)
