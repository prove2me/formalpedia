-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/22737601-ba72-5cda-b34b-9cbfc77a5c0b

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_PowerSeries_dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.DRResolvedModelPackage.smoothOffEdges_smooth ModularCurve.DRResolvedModelPackage.isIntegral ModularCurve.DRResolvedModelPackage.node_fintype ModularCurve.DRResolvedModelPackage.isLocallyNoetherian ModularCurve.DRResolvedModelPackage.node_deq ModularCurve.DRResolvedModelPackage.flat ModularCurve.DRResolvedModelPackage.isProper ModularCurve.DRResolvedModelPackage.toDR_proper ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod MvPolynomial.CrossingQuotient.Resolution.instIsAffineXSchemeOpenCover MvPolynomial.CrossingQuotient.isOpenImmersion_overlapToChartRight MvPolynomial.CrossingQuotient.isOpenImmersion_torusToOverlap MvPolynomial.CrossingQuotient.isLocallyDirected_glueDiagram MvPolynomial.CrossingQuotient.GlueIndex.instPreorder MvPolynomial.CrossingQuotient.isOpenImmersion_torusToChart MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιTorus MvPolynomial.CrossingQuotient.isOpenImmersion_glueMap MvPolynomial.CrossingQuotient.GlueIndex.instLE MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιOverlap MvPolynomial.CrossingQuotient.isLocalization_away_torusRing MvPolynomial.CrossingQuotient.isOpenImmersion_glueDiagram_map MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ι AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.XHDRLevel.bcMap_fst ModularCurve.XHDRLevel.bcMap_snd_assoc ModularCurve.XHDRLevel.bcMap_fst_assoc ModularCurve.XHDRLevel.bcMap_snd ModularCurve.DRResolvedModelPackage.mk.injEq ModularCurve.DRResolvedModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.injEq MazurRapoportAppendix.SpecialFibreComponentTable.mk.sizeOf_spec MazurRapoportAppendix.multiplicityBeta_apply MazurRapoportAppendix.intersectionAlpha_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ MvPolynomial.CrossingQuotient.GlueIndex.chart_le_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus.sizeOf_spec MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_torus MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.ι_toSpec MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing_assoc MvPolynomial.CrossingQuotient.glueMap_torus_overlap MvPolynomial.CrossingQuotient.GlueIndex.chart_le_torus MvPolynomial.CrossingQuotient.glueMap_overlap_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus_le MvPolynomial.CrossingQuotient.Resolution.openCover_f MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing MvPolynomial.CrossingQuotient.glueMap_torus_chart MvPolynomial.CrossingQuotient.glueMap_torus_torus MvPolynomial.CrossingQuotient.glueDiagram_obj MvPolynomial.CrossingQuotient.GlueIndex.chart.injEq MvPolynomial.CrossingQuotient.GlueIndex.chart_le_chart MvPolynomial.CrossingQuotient.GlueIndex.chart.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.openCover_X MvPolynomial.CrossingQuotient.Resolution.openCover_I₀ MvPolynomial.CrossingQuotient.GlueIndex.overlap.injEq MvPolynomial.CrossingQuotient.glueMap_chart_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_overlap MvPolynomial.CrossingQuotient.Resolution.ι_toSpec_assoc MvPolynomial.CrossingQuotient.lift_V MvPolynomial.CrossingQuotient.lift_U MvPolynomial.CrossingQuotient.monomial_neg_natCast MvPolynomial.CrossingQuotient.monomial_zero MvPolynomial.CrossingQuotient.monomial_natCast MvPolynomial.CrossingQuotient.powMap_mk_X RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace DiscCore

open AlgebraicCurve IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField ↥A) Fb]

theorem ord_pow_nat (W : Place L F) (f : F) (n : ℕ) : W.ord (f ^ n) = n * W.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

set_option maxHeartbeats 3200000 in
theorem main (R : RegularProlongation A F Fb) (S : Place L F → Prop) (v : Place (ResidueField ↥A) Fb)
    (Q Q' : Place L F) (t : F) (c : Place L F → ↥A) (B : Subring F)
    (hB : ∀ f : F, f ∈ B ↔ f ∈ R.integers ∧ ∀ W, S W → f ∈ W.toValuationSubring)
    (Φ : ↥B →+* PowerSeries ↥A)
    (ht : t ∈ R.integers)
    (hc : ∀ W, S W → c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap L F (c W : L)) = 1)
    (hinj : ∀ W W', S W → S W' → c W = c W' → W = W')
    (hΦC : ∀ (x : ↥A) (hx : algebraMap L F (x : L) ∈ B), Φ ⟨_, hx⟩ = PowerSeries.C x)
    (hΦX : ∀ hx : t - algebraMap L F (c Q : L) ∈ B, Φ ⟨_, hx⟩ = PowerSeries.X)
    (hR : ∀ (f : ↥B) (hf : (f : F) ∈ R.integers) (k : ℕ),
      (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
      R.residue ⟨f, hf⟩ ≠ 0 ∧ v.ord (R.residue ⟨f, hf⟩) = k)
    (hR' : ∀ (f : ↥B) (hf : (f : F) ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 →
      ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A)
    (S5 : ∀ {n : ℕ} {d e : ↥A} {u G : PowerSeries ↥A}, IsUnit (n : ↥A) → d ∈ maximalIdeal ↥A → e ≠ 0 →
      e • G = u * (PowerSeries.X + PowerSeries.C d) ^ n - PowerSeries.X ^ n →
      ∀ {j : ℕ}, j + 2 ≤ n → d ∣ PowerSeries.coeff j G)
    (hQ : S Q) (hQ' : S Q') (hne : Q' ≠ Q)
    (n : ℕ) (hn : IsUnit (n : ↥A))
    (g : F) (hg : g ∈ R.integers) (hQg : Q.ord g = -(n : ℤ)) (hQ'g : Q'.ord g = n)
    (hWg : ∀ W, S W → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : ↥A) (ε : F) (hε : ε ∈ R.integers) (hεres : R.residue ⟨ε, hε⟩ ≠ 0)
    (hgε : g = 1 + algebraMap L F (e : L) * ε) :
    -1 ≤ v.ord (R.residue ⟨ε, hε⟩) := by
  classical
  have one_notMem : (1 : ↥A) ∉ maximalIdeal ↥A := fun h =>
    (maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr h)

  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, isUnit_zero_iff] at hn
    exact zero_ne_one hn
  have he : e ≠ 0 := by
    rintro rfl
    have h1 : g = 1 := by rw [hgε]; simp
    rw [h1, Place.ord_one] at hQg
    omega
  have heL : (e : L) ≠ 0 := fun h => he (by exact_mod_cast h)
  have hιe : algebraMap L F (e : L) ≠ 0 := (map_ne_zero _).mpr heL
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hQ'g
    omega

  have hιR : ∀ x : ↥A, algebraMap L F (x : L) ∈ R.integers := fun x => (R.algebraMap_mem_iff (x : L)).mpr x.2
  have hιW : ∀ (W : Place L F) (x : L), algebraMap L F x ∈ W.toValuationSubring := fun W x => W.algebraMap_mem' x
  have hιB : ∀ x : ↥A, algebraMap L F (x : L) ∈ B := fun x => (hB _).mpr ⟨hιR x, fun W _ => hιW W x⟩
  have hres_max : ∀ x : ↥A, x ∈ maximalIdeal ↥A → R.residue ⟨algebraMap L F (x : L), hιR x⟩ = 0 := by
    intro x hx
    rw [R.residue_algebraMap x, (IsLocalRing.residue_eq_zero_iff _).mpr hx, map_zero]

  have htne : ∀ b : L, t ≠ algebraMap L F b := by
    intro b hb
    have h1 := (hc Q hQ).2
    rw [hb, ← map_sub, Place.ord_algebraMap] at h1
    exact zero_ne_one h1
  have hsub0 : ∀ b : L, t - algebraMap L F b ≠ 0 := fun b => sub_ne_zero.mpr (htne b)
  have hunit : ∀ W, S W → ∀ b : ↥A, b ≠ c W → W.ord (t - algebraMap L F (b : L)) = 0 := by
    intro W hW b hb
    have h1 : t - algebraMap L F (b : L) = algebraMap L F ((c W : L) - b) + (t - algebraMap L F (c W : L)) := by
      rw [map_sub]; ring
    have hcb : algebraMap L F ((c W : L) - b) ≠ 0 := by
      refine (map_ne_zero _).mpr (sub_ne_zero.mpr ?_)
      exact fun h => hb (by exact_mod_cast h.symm)
    have hord0 : W.ord (algebraMap L F ((c W : L) - b)) = 0 := Place.ord_algebraMap W _
    have hlt : W.ord (algebraMap L F ((c W : L) - b)) < W.ord (t - algebraMap L F (c W : L)) := by
      rw [hord0, (hc W hW).2]; exact zero_lt_one
    rw [h1, Place.ord_add_eq_of_lt W hcb (hsub0 _) hlt, hord0]

  have htW : ∀ W, S W → t ∈ W.toValuationSubring := by
    intro W hW
    have h1 : t - algebraMap L F (c W : L) ∈ W.toValuationSubring :=
      (Place.mem_iff_ord_nonneg W (hsub0 _)).mpr (by rw [(hc W hW).2]; exact zero_le_one)
    simpa using add_mem h1 (hιW W (c W : L))

  obtain ⟨haQ, hordQ⟩ := hc Q hQ
  obtain ⟨haQ', hordQ'⟩ := hc Q' hQ'
  have haa' : c Q ≠ c Q' := fun h => hne (hinj Q Q' hQ hQ' h).symm
  have hdm : c Q - c Q' ∈ maximalIdeal ↥A := sub_mem haQ haQ'

  have hτR : t - algebraMap L F (c Q : L) ∈ R.integers := sub_mem ht (hιR _)
  have hτ'R : t - algebraMap L F (c Q' : L) ∈ R.integers := sub_mem ht (hιR _)
  have hτB : t - algebraMap L F (c Q : L) ∈ B :=
    (hB _).mpr ⟨hτR, fun W hW => sub_mem (htW W hW) (hιW W _)⟩
  have hτ'B : t - algebraMap L F (c Q' : L) ∈ B :=
    (hB _).mpr ⟨hτ'R, fun W hW => sub_mem (htW W hW) (hιW W _)⟩
  have hτ'eq : t - algebraMap L F (c Q' : L) =
      (t - algebraMap L F (c Q : L)) + algebraMap L F ((c Q - c Q' : ↥A) : L) := by
    push_cast; ring

  have hordτQ' : Q'.ord (t - algebraMap L F (c Q : L)) = 0 := hunit Q' hQ' (c Q) haa'
  have hordτ'Q : Q.ord (t - algebraMap L F (c Q' : L)) = 0 := hunit Q hQ (c Q') haa'.symm
  have hordτW : ∀ W, S W → W ≠ Q → W.ord (t - algebraMap L F (c Q : L)) = 0 :=
    fun W hW hWQ => hunit W hW (c Q) fun h => hWQ (hinj W Q hW hQ h.symm)
  have hordτ'W : ∀ W, S W → W ≠ Q' → W.ord (t - algebraMap L F (c Q' : L)) = 0 :=
    fun W hW hWQ' => hunit W hW (c Q') fun h => hWQ' (hinj W Q' hW hQ' h.symm)

  obtain ⟨hτres, hτord⟩ : R.residue ⟨_, hτR⟩ ≠ 0 ∧ v.ord (R.residue ⟨_, hτR⟩) = 1 := by
    refine hR ⟨_, hτB⟩ hτR 1 ?_ ?_
    · intro i hi
      interval_cases i
      rw [hΦX hτB, PowerSeries.coeff_X]; simp
    · rw [hΦX hτB, PowerSeries.coeff_X]; simpa using one_notMem

  have hτ'res : R.residue ⟨_, hτ'R⟩ ≠ 0 := by
    have e1 : (⟨_, hτ'R⟩ : ↥R.integers) = ⟨t, ht⟩ - ⟨_, hιR (c Q')⟩ := Subtype.ext rfl
    have e2 : (⟨_, hτR⟩ : ↥R.integers) = ⟨t, ht⟩ - ⟨_, hιR (c Q)⟩ := Subtype.ext rfl
    rw [e1, map_sub, hres_max _ haQ', sub_zero]
    rw [e2, map_sub, hres_max _ haQ, sub_zero] at hτres
    exact hτres
  have hτ'inv : (t - algebraMap L F (c Q' : L))⁻¹ ∈ R.integers := by
    have hu := R.isUnit_of_residue_ne_zero hτ'res
    have hmul : ((hu.unit⁻¹ : (↥R.integers)ˣ) : ↥R.integers) * (⟨_, hτ'R⟩ : ↥R.integers) = 1 := hu.unit.inv_val
    have hcoe := congrArg (fun z : ↥R.integers => (z : F)) hmul
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at hcoe
    have : ((hu.unit⁻¹ : (↥R.integers)ˣ) : ↥R.integers) = ((t - algebraMap L F (c Q' : L))⁻¹ : F) :=
      eq_inv_of_mul_eq_one_left hcoe
    rw [← this]; exact SetLike.coe_mem _

  have hh0 : g * (t - algebraMap L F (c Q : L)) ^ n * ((t - algebraMap L F (c Q' : L)) ^ n)⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hg0 (pow_ne_zero _ (hsub0 _))) (inv_ne_zero (pow_ne_zero _ (hsub0 _)))
  have hordh : ∀ W, S W →
      W.ord (g * (t - algebraMap L F (c Q : L)) ^ n * ((t - algebraMap L F (c Q' : L)) ^ n)⁻¹) = 0 := by
    intro W hW
    rw [W.ord_mul (mul_ne_zero hg0 (pow_ne_zero _ (hsub0 _))) (inv_ne_zero (pow_ne_zero _ (hsub0 _))),
      W.ord_mul hg0 (pow_ne_zero _ (hsub0 _)), W.ord_inv, ord_pow_nat, ord_pow_nat]
    by_cases hWQ : W = Q
    · subst hWQ; rw [hQg, hordQ, hordτ'Q]; ring
    by_cases hWQ' : W = Q'
    · subst hWQ'; rw [hQ'g, hordQ', hordτQ']; ring
    rw [hWg W hW hWQ hWQ', hordτW W hW hWQ, hordτ'W W hW hWQ']; ring
  have hhB : g * (t - algebraMap L F (c Q : L)) ^ n * ((t - algebraMap L F (c Q' : L)) ^ n)⁻¹ ∈ B := by
    refine (hB _).mpr ⟨?_, fun W hW => (Place.mem_iff_ord_nonneg W hh0).mpr (by rw [hordh W hW])⟩
    rw [← inv_pow]
    exact mul_mem (mul_mem hg (pow_mem hτR _)) (pow_mem hτ'inv _)
  have hgε' : algebraMap L F (e : L) * ε = g - 1 := by rw [hgε]; ring
  have hεeq : ε = (algebraMap L F (e : L))⁻¹ * (g - 1) := by
    rw [← hgε', ← mul_assoc, inv_mul_cancel₀ hιe, one_mul]
  have hFR : ε * (t - algebraMap L F (c Q : L)) ^ n ∈ R.integers := mul_mem hε (pow_mem hτR _)
  have hFB : ε * (t - algebraMap L F (c Q : L)) ^ n ∈ B := by
    refine (hB _).mpr ⟨hFR, fun W hW => ?_⟩
    have hinvW : (algebraMap L F (e : L))⁻¹ ∈ W.toValuationSubring := by
      rw [← map_inv₀]; exact hιW W _
    by_cases hWQ : W = Q
    · subst hWQ
      have hgτ : g * (t - algebraMap L F (c W : L)) ^ n ∈ W.toValuationSubring := by
        refine (Place.mem_iff_ord_nonneg W (mul_ne_zero hg0 (pow_ne_zero _ (hsub0 _)))).mpr ?_
        rw [W.ord_mul hg0 (pow_ne_zero _ (hsub0 _)), ord_pow_nat, hQg, hordQ]; simp
      have : ε * (t - algebraMap L F (c W : L)) ^ n =
          (algebraMap L F (e : L))⁻¹ * (g * (t - algebraMap L F (c W : L)) ^ n - (t - algebraMap L F (c W : L)) ^ n) := by
        rw [hεeq]; ring
      rw [this]
      exact mul_mem hinvW (sub_mem hgτ (pow_mem (sub_mem (htW W hW) (hιW W _)) _))
    · have hgW : g ∈ W.toValuationSubring := by
        refine (Place.mem_iff_ord_nonneg W hg0).mpr ?_
        by_cases hWQ' : W = Q'
        · subst hWQ'; rw [hQ'g]; exact_mod_cast Nat.zero_le n
        · rw [hWg W hW hWQ hWQ']
      have hεW : ε ∈ W.toValuationSubring := by
        rw [hεeq]; exact mul_mem hinvW (sub_mem hgW (one_mem _))
      exact mul_mem hεW (pow_mem (sub_mem (htW W hW) (hιW W _)) _)

  have hid : algebraMap L F (e : L) * (ε * (t - algebraMap L F (c Q : L)) ^ n) =
      g * (t - algebraMap L F (c Q : L)) ^ n * ((t - algebraMap L F (c Q' : L)) ^ n)⁻¹ *
          (t - algebraMap L F (c Q' : L)) ^ n - (t - algebraMap L F (c Q : L)) ^ n := by
    rw [mul_assoc (g * _), inv_mul_cancel₀ (pow_ne_zero _ (hsub0 _)), mul_one, ← mul_assoc, hgε']; ring
  have hidB : (⟨_, hιB e⟩ : ↥B) * ⟨_, hFB⟩ = ⟨_, hhB⟩ * (⟨_, hτB⟩ + ⟨_, hιB (c Q - c Q')⟩) ^ n - ⟨_, hτB⟩ ^ n := by
    apply Subtype.ext
    show algebraMap L F (e : L) * (ε * (t - algebraMap L F (c Q : L)) ^ n) =
      g * (t - algebraMap L F (c Q : L)) ^ n * ((t - algebraMap L F (c Q' : L)) ^ n)⁻¹ *
          ((t - algebraMap L F (c Q : L)) + algebraMap L F ((c Q - c Q' : ↥A) : L)) ^ n -
        (t - algebraMap L F (c Q : L)) ^ n
    rw [← hτ'eq]
    exact hid
  have hΦid := congrArg Φ hidB
  rw [map_mul, map_sub, map_mul, map_pow, map_pow, map_add, hΦC e (hιB e), hΦC _ (hιB (c Q - c Q')),
    hΦX hτB, ← PowerSeries.smul_eq_C_mul] at hΦid

  have hcoef : ∀ j, j + 2 ≤ n → PowerSeries.coeff j (Φ ⟨_, hFB⟩) ∈ maximalIdeal ↥A := by
    intro j hj
    obtain ⟨y, hy⟩ := S5 hn hdm he hΦid hj
    rw [hy]; exact Ideal.mul_mem_right _ _ hdm

  have hFfac : (⟨_, hFR⟩ : ↥R.integers) = ⟨ε, hε⟩ * ⟨_, hτR⟩ ^ n := Subtype.ext (by push_cast; rfl)
  have hFres : R.residue ⟨_, hFR⟩ ≠ 0 := by
    rw [hFfac, map_mul, map_pow]; exact mul_ne_zero hεres (pow_ne_zero _ hτres)
  have hex : ∃ k, PowerSeries.coeff k (Φ ⟨_, hFB⟩) ∉ maximalIdeal ↥A := hR' ⟨_, hFB⟩ hFR hFres
  obtain ⟨-, hordF⟩ := hR ⟨_, hFB⟩ hFR (Nat.find hex) (fun i hi => not_not.mp (Nat.find_min hex hi)) (Nat.find_spec hex)
  have hk : n ≤ Nat.find hex + 1 := by
    by_contra hlt
    exact Nat.find_spec hex (hcoef _ (by omega))
  rw [hFfac, map_mul, map_pow, v.ord_mul hεres (pow_ne_zero _ hτres), ord_pow_nat, hτord] at hordF
  omega

end DiscCore

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    (∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
    (∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) := by
  obtain ⟨hEF, hES⟩ := ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_taylor_and_ord_residue_eq_of_isStrict p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
  have hS5 : ∀ {n : ℕ} {d e : ↥A} {u G : PowerSeries ↥A}, IsUnit (n : ↥A) → d ∈ IsLocalRing.maximalIdeal ↥A → e ≠ 0 →
      e • G = u * (PowerSeries.X + PowerSeries.C d) ^ n - PowerSeries.X ^ n →
      ∀ {j : ℕ}, j + 2 ≤ n → d ∣ PowerSeries.coeff j G :=
    fun hn hd he hF _ hj => PowerSeries.dvd_coeff_of_smul_eq_mul_X_add_C_pow_sub_X_pow hn hd he hF hj
  have hunitA : ∀ n : ℕ, (n : ResidueField ↥A) ≠ 0 → IsUnit (n : ↥A) := by
    intro n hn
    by_contra h
    apply hn
    have hmem : (n : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr h
    have := (IsLocalRing.residue_eq_zero_iff (n : ↥A)).mpr hmem
    rwa [map_natCast] at this
  refine ⟨?_, ?_⟩
  · intro Q Q' hQs hQ's hred hne hv n hnκ g hg₁ hgres hQg hQ'g hWg e ε hε₁ hεres hgε
    obtain ⟨t, c, Φ, ht, hc, hinj, hΦC, hΦX, hT, hR, hR'⟩ := hEF Q hQs hv
    exact DiscCore.main (L := AlgebraicClosure ℚ) Rpd.R₁
      (fun W => Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceFst α hα W = Psp.reduceFst α hα Q)
      (Psp.reduceFst α hα Q) Q Q' t c _
      (fun f => ⟨fun h => ⟨(Subring.mem_inf.mp h).1, fun W hW => Subring.mem_iInf.mp (Subring.mem_inf.mp h).2 ⟨W, hW⟩⟩,
        fun h => Subring.mem_inf.mpr ⟨h.1, Subring.mem_iInf.mpr fun W => h.2 W.1 W.2⟩⟩)
      Φ ht (fun W hW => hc W hW.1 hW.2) (fun W W' hW hW' => hinj W W' hW.1 hW.2 hW'.1 hW'.2) hΦC hΦX hR hR' hS5
      ⟨hQs, rfl⟩ ⟨hQ's, hred⟩ hne n (hunitA n hnκ) g hg₁ hQg hQ'g (fun W hW => hWg W hW.1 hW.2) e ε hε₁ hεres hgε
  · intro Q Q' hQs hQ's hred hne hv n hnκ g hg₁ hgres hQg hQ'g hWg e ε hε₁ hεres hgε
    obtain ⟨t, c, Φ, ht, hc, hinj, hΦC, hΦX, hT, hR, hR'⟩ := hES Q hQs hv
    exact DiscCore.main (L := AlgebraicClosure ℚ) Rpd.R₂
      (fun W => Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
      (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) Q Q' t c _
      (fun f => ⟨fun h => ⟨(Subring.mem_inf.mp h).1, fun W hW => Subring.mem_iInf.mp (Subring.mem_inf.mp h).2 ⟨W, hW⟩⟩,
        fun h => Subring.mem_inf.mpr ⟨h.1, Subring.mem_iInf.mpr fun W => h.2 W.1 W.2⟩⟩)
      Φ ht (fun W hW => hc W hW.1 hW.2) (fun W W' hW hW' => hinj W W' hW.1 hW.2 hW'.1 hW'.2) hΦC hΦX hR hR' hS5
      ⟨hQs, rfl⟩ ⟨hQ's, hred⟩ hne n (hunitA n hnκ) g hg₁ hQg hQ'g (fun W hW => hWg W hW.1 hW.2) e ε hε₁ hεres hgε

end S_ModularCurve_XHDRModelAtP_discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_discLawFst_and_discLawSnd_of_jHPlaceSpecialization_of_offDiag (solution)
