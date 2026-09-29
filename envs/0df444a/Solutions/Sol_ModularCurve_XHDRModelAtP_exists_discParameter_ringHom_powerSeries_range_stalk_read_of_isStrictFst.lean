-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/445d2da2-bad0-5da4-a65f-5f1844ee77bb

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst
import Theorems.Thm_ModularCurve_XHDRModelAtP_readA_mem_integers_and_residue_eq_restrict_comp_of_mem
import Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
import Theorems.Thm_AlgebraicCurve_CurveModel_isRational_pointEquivPlace
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_etale_chart_affineLine_of_isStrictFst
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictFst
import Theorems.Thm_ModularCurve_XHDRModelAtP_section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictFst
import Theorems.Thm_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst
import Theorems.Thm_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section_apply_eq_X
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

universe u v

namespace EtaleExpansion

open Polynomial TensorProduct KaehlerDifferential

section bij
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra S R]
  [IsScalarTower R S R] [Algebra.FormallySmooth R S]

theorem kerCotangentToTensor_bijective (hsurj : Function.Surjective (algebraMap S R)) :
    Function.Bijective (kerCotangentToTensor R S R) := by
  constructor
  · obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection (R := R) (P := S) (A := R) hsurj).mp
      inferInstance
    intro a b hab
    have := congrArg l hab
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hl, LinearMap.id_apply, LinearMap.id_apply] at this
  · haveI : Subsingleton (Ω[R⁄R]) :=
      KaehlerDifferential.subsingleton_of_surjective R R Function.surjective_id
    rw [← LinearMap.range_eq_top, range_kerCotangentToTensor R S R hsurj]
    ext z
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact Subsingleton.elim _ _

noncomputable def cotangentEquiv (hsurj : Function.Surjective (algebraMap S R)) :
    (RingHom.ker (algebraMap S R)).Cotangent ≃ₗ[R] R ⊗[S] Ω[S⁄R] :=
  (LinearEquiv.ofBijective (kerCotangentToTensor R S R) (kerCotangentToTensor_bijective hsurj)).restrictScalars R

theorem cotangentEquiv_toCotangent (hsurj : Function.Surjective (algebraMap S R)) (x) :
    cotangentEquiv hsurj ((RingHom.ker (algebraMap S R)).toCotangent x) = 1 ⊗ₜ D R S x.1 := rfl

end bij

section omega
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [Algebra R[X] S] [Algebra R S] [IsScalarTower R R[X] S] [Algebra.FormallyEtale R[X] S]

theorem exists_basis_kaehler :
    ∃ b : Module.Basis (Fin 1) S (Ω[S⁄R]), b 0 = D R S (algebraMap R[X] S X) := by
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale R R[X] S
  let bX : Module.Basis (Fin 1) R[X] (Ω[R[X]⁄R]) :=
    (Module.Basis.singleton (Fin 1) R[X]).map (polynomialEquiv R).symm
  have hbX : bX 0 = D R R[X] X := by
    simp [bX, KaehlerDifferential.polynomialEquiv_symm]
  refine ⟨(Algebra.TensorProduct.basis S bX).map hbc.equiv, ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, hbX, IsBaseChange.equiv_tmul, one_smul,
    KaehlerDifferential.map_D]

theorem exists_basis_cotangent (χ : S →ₐ[R] R)
    (ht₀ : algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X)) ∈ RingHom.ker χ.toRingHom) :
    ∃ b : Module.Basis (Fin 1) R (RingHom.ker χ.toRingHom).Cotangent,
      b 0 = (RingHom.ker χ.toRingHom).toCotangent ⟨_, ht₀⟩ := by
  letI alg : Algebra S R := χ.toRingHom.toAlgebra
  haveI hst : IsScalarTower R S R := IsScalarTower.of_algebraMap_eq (fun r => (χ.commutes r).symm)
  have hsurj : Function.Surjective (algebraMap S R) := fun r => ⟨algebraMap R S r, χ.commutes r⟩
  haveI : Algebra.FormallySmooth R S := Algebra.FormallySmooth.comp R R[X] S
  obtain ⟨bΩ, hbΩ⟩ := exists_basis_kaehler (R := R) (S := S)
  let bRΩ : Module.Basis (Fin 1) R (R ⊗[S] Ω[S⁄R]) := Algebra.TensorProduct.basis R bΩ
  have hbRΩ : bRΩ 0 = (1 : R) ⊗ₜ[S] D R S (algebraMap R[X] S X) := by
    rw [Algebra.TensorProduct.basis_apply, hbΩ]
  refine ⟨bRΩ.map (cotangentEquiv hsurj).symm, ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.symm_apply_eq, hbRΩ, eq_comm]
  show cotangentEquiv hsurj ((RingHom.ker (algebraMap S R)).toCotangent ⟨_, ht₀⟩) = _
  rw [cotangentEquiv_toCotangent]
  simp only [map_sub, Derivation.map_algebraMap, sub_zero]

theorem exists_powerSeries_expansion [Nontrivial R] (χ : S →ₐ[R] R) :
    ∃ Θ : S →+* PowerSeries R,
      (∀ r : R, Θ (algebraMap R S r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (s : S), (∀ k : ℕ, k < n → PowerSeries.coeff k (Θ s) = 0) ↔
        s ∈ RingHom.ker χ.toRingHom ^ n) ∧
      (∀ (n : ℕ) (q : PowerSeries R), ∃ s : S, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (Θ s) = PowerSeries.coeff k q) ∧
      Θ (algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X))) = PowerSeries.X := by
  have hχt₀ : χ (algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X))) = 0 := by
    simp
  have ht₀ : algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X)) ∈ RingHom.ker χ.toRingHom := hχt₀
  obtain ⟨b, hb⟩ := exists_basis_cotangent χ ht₀
  haveI : Module.Free R (RingHom.ker χ.toRingHom).Cotangent := Module.Free.of_basis b
  have he : Module.finrank R (RingHom.ker χ.toRingHom).Cotangent = 1 := by
    simpa using Module.finrank_eq_card_basis b
  haveI : Algebra.FormallySmooth R S := Algebra.FormallySmooth.comp R R[X] S
  refine Algebra.FormallySmooth.exists_powerSeries_expansion_along_section_apply_eq_X χ he _ hχt₀ ?_
  intro y hy
  obtain ⟨r, hr⟩ : ∃ r : R, (RingHom.ker χ.toRingHom).toCotangent ⟨y, hy⟩ = r • b 0 := by
    refine ⟨b.repr ((RingHom.ker χ.toRingHom).toCotangent ⟨y, hy⟩) 0, ?_⟩
    conv_lhs => rw [← b.sum_repr ((RingHom.ker χ.toRingHom).toCotangent ⟨y, hy⟩)]
    simp
  rw [hb, ← algebraMap_smul S, ← map_smul, Ideal.toCotangent_eq] at hr
  have h2 : y - algebraMap R S r * (algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X))) ∈
      RingHom.ker χ.toRingHom ^ 2 := by
    first | simpa [smul_eq_mul] using hr | simpa [Submodule.coe_smul, smul_eq_mul] using hr | exact hr
  have hdecomp : y = algebraMap R S r * (algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X))) +
      (y - algebraMap R S r * (algebraMap R[X] S X - algebraMap R S (χ (algebraMap R[X] S X)))) := by ring
  rw [hdecomp]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)) h2

end omega

end EtaleExpansion

namespace EtaleExpansion

p2m_open "CategoryTheory AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial TopologicalSpace"

section stalk

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {X : Scheme.{u}} (U : X.Opens) (x₀ : X) (hxU : x₀ ∈ U)
  (f : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of A[X]))

omit [IsLocalRing A] in

theorem SpecMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (g : R ⟶ S) (r : R) :
    (Spec.map g).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (g r) := by
  have h := congrArg (fun k => k.hom r) (Scheme.ΓSpecIso_inv_naturality g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

noncomputable def chartToStalk : A[X] →+* (X.presheaf.stalk x₀ : Type u) :=
  (U.stalkIso ⟨x₀, hxU⟩).hom.hom.comp
    ((f.stalkMap ⟨x₀, hxU⟩).hom.comp (StructureSheaf.toStalk A[X] (f.base ⟨x₀, hxU⟩)).hom)

theorem chartToStalk_apply (q : A[X]) :
    chartToStalk U x₀ hxU f q =
      X.presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩
        ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv q))) := by
  rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
  show (U.stalkIso ⟨x₀, hxU⟩).hom ((f.stalkMap ⟨x₀, hxU⟩) (StructureSheaf.toStalk A[X] (f.base ⟨x₀, hxU⟩) q)) =
    X.presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv q))
  have h1 : StructureSheaf.toStalk A[X] (f.base ⟨x₀, hxU⟩) q =
      (Spec (CommRingCat.of A[X])).presheaf.germ ⊤ (f.base ⟨x₀, hxU⟩) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv q) := by
    rw [← StructureSheaf.algebraMap_germ ⊤ _ trivial, Scheme.ΓSpecIso_inv]
    rfl
  rw [h1, Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply, Scheme.Opens.germ_stalkIso_hom]
  rfl

theorem formallyEtale_chartToStalk [Etale f] :
    (chartToStalk U x₀ hxU f).FormallyEtale := by
  let St : Type u := ((Spec (CommRingCat.of A[X])).presheaf.stalk (f.base ⟨x₀, hxU⟩) : Type u)
  let SU : Type u := ((U : Scheme.{u}).presheaf.stalk ⟨x₀, hxU⟩ : Type u)
  letI algSt : Algebra A[X] St := (StructureSheaf.toStalk A[X] (f.base ⟨x₀, hxU⟩)).hom.toAlgebra
  haveI : IsLocalization.AtPrime St (f.base ⟨x₀, hxU⟩).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A[X] (f.base ⟨x₀, hxU⟩)
  haveI fe1 : Algebra.FormallyEtale A[X] St :=
    Algebra.FormallyEtale.of_isLocalization (f.base ⟨x₀, hxU⟩).asIdeal.primeCompl
  letI algSU : Algebra St SU := (f.stalkMap ⟨x₀, hxU⟩).hom.toAlgebra
  haveI : Algebra.FormallyUnramified St SU := FormallyUnramified.stalkMap f ⟨x₀, hxU⟩
  haveI : Algebra.FormallySmooth St SU := by
    have hmem : (⟨x₀, hxU⟩ : (U : Scheme.{u})) ∈ f.smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]; trivial
    exact (Scheme.Hom.mem_smoothLocus).mp hmem
  haveI fe2 : Algebra.FormallyEtale St SU := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  letI algASU : Algebra A[X] SU :=
    ((f.stalkMap ⟨x₀, hxU⟩).hom.comp (StructureSheaf.toStalk A[X] (f.base ⟨x₀, hxU⟩)).hom).toAlgebra
  haveI : IsScalarTower A[X] St SU := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI fe3 : Algebra.FormallyEtale A[X] SU := Algebra.FormallyEtale.comp A[X] St SU
  letI algAS : Algebra A[X] (X.presheaf.stalk x₀ : Type u) := (chartToStalk U x₀ hxU f).toAlgebra
  let e : SU ≃ₐ[A[X]] (X.presheaf.stalk x₀ : Type u) :=
    AlgEquiv.ofRingEquiv (f := (U.stalkIso ⟨x₀, hxU⟩).commRingCatIsoToRingEquiv) (fun q => rfl)
  exact Algebra.FormallyEtale.of_equiv e

theorem stalkClosedPointTo_chartToStalk
    (sQ : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u})) (χQ : A[X] →+* A)
    (hsQf : sQ ≫ f = Spec.map (CommRingCat.ofHom χQ))
    (ut : Spec (CommRingCat.of A) ⟶ X) (hut : sQ ≫ U.ι = ut)
    (hx : ut.base (IsLocalRing.closedPoint A) = x₀) (q : A[X]) :
    Scheme.stalkClosedPointTo ut
      (X.presheaf.stalkSpecializes (specializes_of_eq hx) (chartToStalk U x₀ hxU f q)) = χQ q := by
  subst hut
  rw [chartToStalk_apply, Scheme.Opens.ι_appIso, Iso.refl_inv]
  show Scheme.stalkClosedPointTo (sQ ≫ U.ι) (X.presheaf.stalkSpecializes (specializes_of_eq hx)
    (X.presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv q)))) = χQ q
  have hmem : (sQ ≫ U.ι).base (IsLocalRing.closedPoint A) ∈ U.ι ''ᵁ ⊤ :=
    ⟨sQ.base (IsLocalRing.closedPoint A), trivial, rfl⟩
  have key : ∀ w, (X.presheaf.stalkSpecializes (specializes_of_eq hx))
      (X.presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩ w) =
        X.presheaf.germ (U.ι ''ᵁ ⊤) ((sQ ≫ U.ι).base (IsLocalRing.closedPoint A)) hmem w := fun w => by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [key, ← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo]

  have e₁ : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤ (sQ ≫ U.ι) ⁻¹ᵁ (U.ι ''ᵁ ⊤) := by
    rintro q -
    exact ⟨sQ.base q, trivial, rfl⟩
  have step : (sQ ≫ U.ι).app (U.ι ''ᵁ ⊤) ≫
      ((Spec (CommRingCat.of A)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem (sQ ≫ U.ι) hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of A)).hom =
      sQ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom := by
    rw [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, ← Category.assoc]
    congr 1
    have hU : U.ι.appLE (U.ι ''ᵁ ⊤) ⊤ (fun q _ => ⟨q, trivial, rfl⟩) = 𝟙 _ := by
      rw [Scheme.Opens.ι_appLE]
      exact X.presheaf.map_id _
    calc (sQ ≫ U.ι).app (U.ι ''ᵁ ⊤) ≫ (Spec (CommRingCat.of A)).presheaf.map
          (eqToHom (Scheme.preimage_eq_top_of_closedPoint_mem (sQ ≫ U.ι) hmem).symm).op
        = (sQ ≫ U.ι).appLE (U.ι ''ᵁ ⊤) ⊤ e₁ := by
          rw [Scheme.Hom.appLE]; rfl
      _ = U.ι.appLE (U.ι ''ᵁ ⊤) ⊤ (fun q _ => ⟨q, trivial, rfl⟩) ≫ sQ.appLE ⊤ ⊤ le_rfl := by
          rw [Scheme.Hom.appLE_comp_appLE]
      _ = sQ.appTop := by
          rw [hU]; erw [Category.id_comp]; exact (Scheme.Hom.app_eq_appLE sQ).symm
  have step' : ∀ w, ((sQ ≫ U.ι).app (U.ι ''ᵁ ⊤) ≫
      ((Spec (CommRingCat.of A)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem (sQ ≫ U.ι) hmem).symm).op ≪≫
        Scheme.ΓSpecIso (CommRingCat.of A)).hom) w = (Scheme.ΓSpecIso (CommRingCat.of A)).hom (sQ.appTop w) :=
    fun w => by rw [step]; rfl
  rw [step']
  have h2 : sQ.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv q)) =
      (sQ ≫ f).appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv q) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [h2, hsQf, SpecMap_appTop_ΓSpecIso_inv]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem chartToStalk_algebraMap (πA : X ⟶ Spec (CommRingCat.of A))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X])) = U.ι ≫ πA) (a : A) :
    chartToStalk U x₀ hxU f (algebraMap A A[X] a) =
      X.presheaf.germ ⊤ x₀ trivial (πA.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) := by
  rw [chartToStalk_apply, Scheme.Opens.ι_appIso, Iso.refl_inv]
  show X.presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv (algebraMap A A[X] a))) = _
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A[X])).inv (algebraMap A A[X] a) =
      (Spec.map (CommRingCat.ofHom (algebraMap A A[X]))).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    rfl
  rw [h1, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hover, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, Scheme.Opens.ι_appTop]
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _

theorem exists_powerSeries_expansion_stalk [Etale f] (πA : X ⟶ Spec (CommRingCat.of A))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X])) = U.ι ≫ πA)
    (sQ : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u})) (χQ : A[X] →+* A)
    (hsQover : sQ ≫ U.ι ≫ πA = 𝟙 _)
    (hsQf : sQ ≫ f = Spec.map (CommRingCat.ofHom χQ))
    (ut : Spec (CommRingCat.of A) ⟶ X) (hut : sQ ≫ U.ι = ut)
    (hx : ut.base (IsLocalRing.closedPoint A) = x₀) :
    ∃ Θ : (X.presheaf.stalk x₀ : Type u) →+* PowerSeries A,
      (∀ a : A, Θ (X.presheaf.germ ⊤ x₀ trivial (πA.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
        PowerSeries.C a) ∧
      (∀ (n : ℕ) (b : (X.presheaf.stalk x₀ : Type u)), (∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = 0) ↔
        b ∈ RingHom.ker ((Scheme.stalkClosedPointTo ut).hom.comp
          (X.presheaf.stalkSpecializes (specializes_of_eq hx)).hom) ^ n) ∧
      (∀ (n : ℕ) (q : PowerSeries A), ∃ b : (X.presheaf.stalk x₀ : Type u), ∀ k : ℕ, k < n →
        PowerSeries.coeff k (Θ b) = PowerSeries.coeff k q) ∧
      Θ (X.presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩
            ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv Polynomial.X))) -
          X.presheaf.germ ⊤ x₀ trivial (πA.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (χQ Polynomial.X)))) =
        PowerSeries.X := by

  have hχC : ∀ a, χQ (algebraMap A A[X] a) = a := by
    have h : Spec.map (CommRingCat.ofHom χQ) ≫ Spec.map (CommRingCat.ofHom (algebraMap A A[X])) = 𝟙 _ := by
      rw [← hsQf, Category.assoc, hover, ← Category.assoc, hut, ← hsQover, ← hut, Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id] at h
    have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    intro a
    exact DFunLike.congr_fun h' a
  letI algAS : Algebra A[X] (X.presheaf.stalk x₀ : Type u) := (chartToStalk U x₀ hxU f).toAlgebra
  letI algA : Algebra A (X.presheaf.stalk x₀ : Type u) :=
    ((chartToStalk U x₀ hxU f).comp (algebraMap A A[X])).toAlgebra
  haveI : IsScalarTower A A[X] (X.presheaf.stalk x₀ : Type u) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FormallyEtale A[X] (X.presheaf.stalk x₀ : Type u) := formallyEtale_chartToStalk U x₀ hxU f
  let χ' : (X.presheaf.stalk x₀ : Type u) →ₐ[A] A :=
    { toRingHom := (Scheme.stalkClosedPointTo ut).hom.comp (X.presheaf.stalkSpecializes (specializes_of_eq hx)).hom
      commutes' := fun a => by
        show Scheme.stalkClosedPointTo ut (X.presheaf.stalkSpecializes (specializes_of_eq hx)
          (chartToStalk U x₀ hxU f (algebraMap A A[X] a))) = a
        rw [stalkClosedPointTo_chartToStalk U x₀ hxU f sQ χQ hsQf ut hut hx, hχC] }
  obtain ⟨Θ, h1, h2, h3, h4⟩ := exists_powerSeries_expansion (R := A) (S := (X.presheaf.stalk x₀ : Type u)) χ'
  refine ⟨Θ, ?_, h2, h3, ?_⟩
  · intro a
    rw [← chartToStalk_algebraMap U x₀ hxU f πA hover]
    exact h1 a
  · have e2 : χ' (algebraMap A[X] (X.presheaf.stalk x₀ : Type u) Polynomial.X) = χQ Polynomial.X :=
      stalkClosedPointTo_chartToStalk U x₀ hxU f sQ χQ hsQf ut hut hx Polynomial.X
    rw [e2] at h4
    rw [← chartToStalk_apply, ← chartToStalk_algebraMap U x₀ hxU f πA hover]
    exact h4

end stalk

end EtaleExpansion

namespace EtaleExpansion

open CategoryTheory AlgebraicGeometry TopologicalSpace

section reading

theorem stalkMap_stalkMap_stalkSpecializes_germ {C Y X : Scheme.{u}} (e : C ⟶ Y) (g : Y ⟶ X)
    (ξ : C) (x₀ : X) (hsp : g.base (e.base ξ) ⤳ x₀) (W : X.Opens) (hW : x₀ ∈ W) (w : Γ(X, W)) :
    e.stalkMap ξ (g.stalkMap (e.base ξ) (X.presheaf.stalkSpecializes hsp (X.presheaf.germ W x₀ hW w))) =
      C.presheaf.germ (e ⁻¹ᵁ (g ⁻¹ᵁ W)) ξ (hsp.mem_open W.2 hW) (e.app (g ⁻¹ᵁ W) (g.app W w)) := by
  have h1 : X.presheaf.stalkSpecializes hsp (X.presheaf.germ W x₀ hW w) =
      X.presheaf.germ W (g.base (e.base ξ)) (hsp.mem_open W.2 hW) w := by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [h1, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]

theorem injective_stalkMap_stalkMap_stalkSpecializes {C Y X : Scheme.{u}} [IsIntegral X] [IrreducibleSpace C]
    (e : C ⟶ Y) (g : Y ⟶ X) [IsOpenImmersion (e ≫ g)] (x₀ : X)
    (hsp : g.base (e.base (genericPoint C)) ⤳ x₀) :
    Function.Injective (fun b => e.stalkMap (genericPoint C) (g.stalkMap (e.base (genericPoint C))
      (X.presheaf.stalkSpecializes hsp b))) := by
  have hη : g.base (e.base (genericPoint C)) = genericPoint X := genericPoint_eq_of_isOpenImmersion (e ≫ g)
  have hinj1 : ∀ (y : X) (h : y ⤳ x₀), y = genericPoint X → Function.Injective (X.presheaf.stalkSpecializes h) := by
    rintro _ h rfl
    exact IsFractionRing.injective (X.presheaf.stalk x₀) X.functionField
  have hinj2 : Function.Injective ((e ≫ g).stalkMap (genericPoint C)) :=
    (asIso ((e ≫ g).stalkMap (genericPoint C))).commRingCatIsoToRingEquiv.injective
  intro a b hab
  apply hinj1 _ hsp hη
  apply hinj2
  simp only [Scheme.Hom.stalkMap_comp, CommRingCat.comp_apply]
  exact hab

theorem stalkClosedPointTo_germ {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}} (ut : Spec R ⟶ X)
    (V : X.Opens) (hV : ut.base (IsLocalRing.closedPoint R) ∈ V) (s : Γ(X, V)) :
    Scheme.stalkClosedPointTo ut (X.presheaf.germ V _ hV s) =
      (Scheme.ΓSpecIso R).hom (ut.appLE V ⊤
        (by rw [Scheme.preimage_eq_top_of_closedPoint_mem ut hV]) s) := by
  rw [← CommRingCat.comp_apply, Scheme.germ_stalkClosedPointTo]
  show (Scheme.ΓSpecIso R).hom ((Spec R).presheaf.map
    (eqToHom (Scheme.preimage_eq_top_of_closedPoint_mem ut hV).symm).op (ut.app V s)) = _
  congr 1

theorem appLE_congr_hom {X' Y' : Scheme.{u}} {m m' : X' ⟶ Y'} (h : m = m') (U₁ : Y'.Opens) (V₁ : X'.Opens)
    (e : V₁ ≤ m ⁻¹ᵁ U₁) (e' : V₁ ≤ m' ⁻¹ᵁ U₁) (x : Γ(Y', U₁)) :
    m.appLE U₁ V₁ e x = m'.appLE U₁ V₁ e' x := by
  subst h; rfl

end reading

section curve

open AlgebraicCurve

variable {L : Type} [Field L] [Algebra (AlgebraicClosure ℚ) L] (Mdl : CurveModel (AlgebraicClosure ℚ) L)
  (A : ValuationSubring (AlgebraicClosure ℚ))
  {Y X : Scheme.{0}} (e : Mdl.C ⟶ Y) (g : Y ⟶ X) (x₀ : X)
  (hsp : g.base (e.base (genericPoint Mdl.C)) ⤳ x₀)

theorem ffEquiv_symm_reading_mem_and_sub_value_mem_nonunits
    (ut : Spec (CommRingCat.of ↥A) ⟶ X) (hx : ut.base (IsLocalRing.closedPoint ↥A) = x₀)
    (Q : Place (AlgebraicClosure ℚ) L)
    (hgen : (Mdl.pointEquivPlace.symm Q).1 ≫ e ≫ g = Spec.map (CommRingCat.ofHom A.subtype) ≫ ut)
    (b : X.presheaf.stalk x₀) :
    Mdl.ffEquiv.symm (e.stalkMap (genericPoint Mdl.C) (g.stalkMap (e.base (genericPoint Mdl.C))
        (X.presheaf.stalkSpecializes hsp b))) ∈ Q.toValuationSubring ∧
    Mdl.ffEquiv.symm (e.stalkMap (genericPoint Mdl.C) (g.stalkMap (e.base (genericPoint Mdl.C))
        (X.presheaf.stalkSpecializes hsp b))) -
      algebraMap (AlgebraicClosure ℚ) L ((Scheme.stalkClosedPointTo ut
        (X.presheaf.stalkSpecializes (specializes_of_eq hx) b) : ↥A) : AlgebraicClosure ℚ) ∈
      Q.toValuationSubring.nonunits := by
  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.germ_exist (x := x₀) b
  rw [stalkMap_stalkMap_stalkSpecializes_germ]
  set z := Mdl.pointEquivPlace.symm Q with hz_def
  have hzQ : Mdl.pointEquivPlace z = Q := Equiv.apply_symm_apply _ _

  have hutV : ∀ q : Spec (CommRingCat.of ↥A), ut.base q ∈ V := fun q =>
    ((IsLocalRing.specializes_closedPoint q).map ut.base.hom.continuous).mem_open V.2 (hx ▸ hxV)
  have hz : ⊤ ≤ z.1 ⁻¹ᵁ (e ⁻¹ᵁ (g ⁻¹ᵁ V)) := by
    rintro q -
    show ((z.1 ≫ e) ≫ g).base q ∈ V
    rw [Category.assoc, hgen]
    exact hutV _
  haveI : Nonempty (Scheme.Opens.toScheme (e ⁻¹ᵁ (g ⁻¹ᵁ V))) := ⟨⟨genericPoint Mdl.C, hsp.mem_open V.2 hxV⟩⟩
  obtain ⟨hmem, hnon⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
      Mdl (e ⁻¹ᵁ (g ⁻¹ᵁ V)) (e.app (g ⁻¹ᵁ V) (g.app V s)) z hz
  rw [hzQ] at hmem hnon
  refine ⟨hmem, ?_⟩

  have hval : (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).hom
      (z.1.appLE (e ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ hz (e.app (g ⁻¹ᵁ V) (g.app V s))) =
      ((Scheme.stalkClosedPointTo ut (X.presheaf.stalkSpecializes (specializes_of_eq hx)
        (X.presheaf.germ V x₀ hxV s)) : ↥A) : AlgebraicClosure ℚ) := by

    have r1 : X.presheaf.stalkSpecializes (specializes_of_eq hx) (X.presheaf.germ V x₀ hxV s) =
        X.presheaf.germ V (ut.base (IsLocalRing.closedPoint ↥A)) (hx ▸ hxV) s := by
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rw [r1, stalkClosedPointTo_germ]

    have H₁ : (⊤ : (Spec (CommRingCat.of (AlgebraicClosure ℚ))).Opens) ≤ (z.1 ≫ e ≫ g) ⁻¹ᵁ V := by
      rw [hgen]; rintro q -; exact hutV _
    have l1 : z.1.appLE (e ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ hz (e.app (g ⁻¹ᵁ V) (g.app V s)) =
        (z.1 ≫ e ≫ g).appLE V ⊤ H₁ s := by
      have := Scheme.Hom.appLE_comp_appLE z.1 (e ≫ g) V (e ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ le_rfl hz
      have hh : (e ≫ g).appLE V (e ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl s = e.app (g ⁻¹ᵁ V) (g.app V s) := by
        show (e ≫ g).appLE V ((e ≫ g) ⁻¹ᵁ V) le_rfl s = _
        rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.comp_app]
        rfl
      rw [← hh, ← CommRingCat.comp_apply, this]
    have e₂ : (⊤ : (Spec (CommRingCat.of (AlgebraicClosure ℚ))).Opens) ≤
        (Spec.map (CommRingCat.ofHom A.subtype) ≫ ut) ⁻¹ᵁ V := by rintro q -; exact hutV _
    have l2 : (z.1 ≫ e ≫ g).appLE V ⊤ H₁ s =
        (Spec.map (CommRingCat.ofHom A.subtype) ≫ ut).appLE V ⊤ e₂ s := appLE_congr_hom hgen V ⊤ _ _ s
    have l3 : (Spec.map (CommRingCat.ofHom A.subtype) ≫ ut).appLE V ⊤ e₂ s =
        (Spec.map (CommRingCat.ofHom A.subtype)).appTop (ut.appLE V ⊤ (fun q _ => hutV q) s) := by
      have := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom A.subtype)) ut V ⊤ ⊤ (fun q _ => hutV q) le_top
      rw [← this, CommRingCat.comp_apply]
      show (Spec.map (CommRingCat.ofHom A.subtype)).appLE ⊤ ((Spec.map (CommRingCat.ofHom A.subtype)) ⁻¹ᵁ ⊤) le_rfl
        (ut.appLE V ⊤ (fun q _ => hutV q) s) = _
      rw [Scheme.Hom.appLE_eq_app]
      rfl
    rw [l1, l2, l3, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    rfl
  rw [hval] at hnon
  exact hnon

theorem ffEquiv_symm_reading_baseGerm (πA : X ⟶ Spec (CommRingCat.of ↥A))
    (hbase : e ≫ g ≫ πA = Mdl.toBase ≫ Spec.map (CommRingCat.ofHom A.subtype)) (a : ↥A) :
    Mdl.ffEquiv.symm (e.stalkMap (genericPoint Mdl.C) (g.stalkMap (e.base (genericPoint Mdl.C))
        (X.presheaf.stalkSpecializes hsp
          (X.presheaf.germ ⊤ x₀ trivial (πA.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)))))) =
      algebraMap (AlgebraicClosure ℚ) L (a : AlgebraicClosure ℚ) := by
  rw [stalkMap_stalkMap_stalkSpecializes_germ]
  have h1 : (e.app (g ⁻¹ᵁ ⊤)) ((g.app ⊤) (πA.appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) =
      (e ≫ g ≫ πA).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a) := by
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rfl
  rw [h1, hbase, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, SpecMap_appTop_ΓSpecIso_inv,
    RingEquiv.symm_apply_eq, Mdl.ffEquiv_algebraMap]
  rfl

end curve

section taylor

open AlgebraicCurve

theorem maximalIdeal_eq_span_of_ord_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (Q : Place K F) {t : F} (ht : t ∈ Q.toValuationSubring) (hord : Q.ord t = 1) :
    IsLocalRing.maximalIdeal ↥Q.toValuationSubring = Ideal.span {(⟨t, ht⟩ : ↥Q.toValuationSubring)} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥Q.toValuationSubring
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at hord
  obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow ht0 hϖ
  rw [hord, zpow_one] at hu
  have htt : (⟨t, ht⟩ : ↥Q.toValuationSubring) = (u : ↥Q.toValuationSubring) * ϖ := by
    apply Subtype.ext
    simpa using hu
  have hirr : Irreducible (⟨t, ht⟩ : ↥Q.toValuationSubring) := by
    rw [htt]
    exact (associated_unit_mul_left ϖ (u : ↥Q.toValuationSubring) u.isUnit).symm.irreducible hϖ
  exact hirr.maximalIdeal_eq

theorem exists_mem_pow_eq_pow_mul {S K F : Type*} [CommRing S] [Field K] [Field F] [Algebra K F]
    (Q : Place K F) (emb : S →+* F) (hO : ∀ b, emb b ∈ Q.toValuationSubring)
    (I : Ideal S) (hI : ∀ b ∈ I, emb b ∈ Q.toValuationSubring.nonunits)
    {t : F} (ht : t ∈ Q.toValuationSubring) (hord : Q.ord t = 1)
    (k : ℕ) (d : S) (hd : d ∈ I ^ k) :
    ∃ r ∈ Q.toValuationSubring, emb d = t ^ k * r := by
  let embO : S →+* ↥Q.toValuationSubring := emb.codRestrict Q.toValuationSubring hO
  have hle : I.map embO ≤ IsLocalRing.maximalIdeal ↥Q.toValuationSubring := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact ValuationSubring.coe_mem_nonunits_iff.mp (hI b hb)
  have hmem : embO d ∈ Ideal.span {(⟨t, ht⟩ : ↥Q.toValuationSubring) ^ k} := by
    rw [← Ideal.span_singleton_pow, ← maximalIdeal_eq_span_of_ord_eq_one Q ht hord]
    refine Ideal.pow_right_mono hle k ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hd
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨(r : F), r.2, ?_⟩
  rw [mul_comm]
  show ((embO d : ↥Q.toValuationSubring) : F) = _
  rw [← hr]
  simp

end taylor

end EtaleExpansion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

set_option maxHeartbeats 3200000 in

theorem EtaleExpansion.expan_of_etaleChart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (x₀ : ↥(XO (ΓM M H) hj ρ))

    (prA : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ)
    (hprA : prA = (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ))
    (hsp : prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀)

    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : x₀ ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _)
    (het : Etale f)
    (hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤)))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (sQ : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})) (χQ : Polynomial ↥A →+* ↥A)
    (hsQover : sQ ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsQgen : barPt A ≫ sQ ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ prA)
    (hsQf : sQ ≫ f = Spec.map (CommRingCat.ofHom χQ))
    (ut : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ) (hut : sQ ≫ U.ι = ut)
    (hx : ut.base (IsLocalRing.closedPoint ↥A) = x₀)

    (hparamO : (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) ∈ Q.toValuationSubring)
    (hord : Q.ord ((((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ)) = 1) :
    ∃ (Φ : ↥(((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range) →+* PowerSeries ↥A)
      (Θ : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* PowerSeries ↥A),
      (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
      (∀ ht : (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ) ∈ ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range, Φ ⟨_, ht⟩ = PowerSeries.X) ∧
      (∀ (g : ↥(((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range)) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (g : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ g) : ↥A) : AlgebraicClosure ℚ) *
              ((((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ)) ^ i =
            ((((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ)) ^ k * r) ∧
      (∀ b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀), Φ ⟨((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))) b, ⟨b, rfl⟩⟩ = Θ b) ∧
      (∀ a : ↥A, Θ (baseGerm ρ x₀ a) = PowerSeries.C a) ∧
      (∀ (n : ℕ) (b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀)),
        (∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = 0) ↔ b ∈ RingHom.ker ((Scheme.stalkClosedPointTo ut).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom) ^ n) ∧
      (∀ (n : ℕ) (q : PowerSeries ↥A), ∃ b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀),
        ∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = PowerSeries.coeff k q) := by

  have hgA₁ : (𝔛.eeta ≫ prA) ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ := by
    rw [hprA, Category.assoc, pullback.lift_fst, Category.comp_id]
  have hgA₂ : (𝔛.eeta ≫ prA) ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A := by
    rw [hprA, Category.assoc, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
  obtain ⟨hint, -, hoi⟩ :=
    ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 ρ hρ (𝔛.eeta ≫ prA) hgA₁ hgA₂
  haveI := hint
  haveI := hoi
  haveI := het

  obtain ⟨Θ, hΘC, hΘfil, hΘsurj, hΘX⟩ :=
    EtaleExpansion.exists_powerSeries_expansion_stalk U x₀ hxU f (pullback.snd _ _) hover sQ χQ hsQover hsQf ut hut hx

  set emb : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥(xHFunctionFieldBar M H) := ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))) with hemb_def
  have hemb : ∀ b, emb b = (𝔛.Meta).ffEquiv.symm (𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)
      (prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))
        ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp b))) := fun b => rfl
  have hinj : Function.Injective emb := by
    intro a b hab
    apply EtaleExpansion.injective_stalkMap_stalkMap_stalkSpecializes 𝔛.eeta prA x₀ hsp
    apply (𝔛.Meta).ffEquiv.symm.injective
    rw [← hemb, ← hemb]
    exact hab
  have hgen' : ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ prA = barPt A ≫ ut := by
    rw [← hsQgen, hut]
  have hval : ∀ b, emb b ∈ Q.toValuationSubring ∧ emb b - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)
      ((Scheme.stalkClosedPointTo ut ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx) b) : ↥A) :
        AlgebraicClosure ℚ) ∈ Q.toValuationSubring.nonunits := fun b =>
    EtaleExpansion.ffEquiv_symm_reading_mem_and_sub_value_mem_nonunits (𝔛.Meta) A 𝔛.eeta prA x₀ hsp ut hx Q hgen' b
  have hO : ∀ b, emb b ∈ Q.toValuationSubring := fun b => (hval b).1
  have hK : ∀ b ∈ RingHom.ker ((Scheme.stalkClosedPointTo ut).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom), emb b ∈ Q.toValuationSubring.nonunits := by
    intro b hb
    have h2 := (hval b).2
    have hb' : Scheme.stalkClosedPointTo ut ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx) b) = 0 := hb
    rw [hb'] at h2
    simpa using h2
  have hbase : 𝔛.eeta ≫ prA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
    rw [← Category.assoc]; exact hgA₂
  have hembC : ∀ a : ↥A, emb (baseGerm ρ x₀ a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) :=
    fun a => EtaleExpansion.ffEquiv_symm_reading_baseGerm (𝔛.Meta) A 𝔛.eeta prA x₀ hsp (pullback.snd _ _) hbase a
  have hembT : emb ((XO (ΓM M H) hj ρ).presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩ ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) = (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) := by
    rw [hemb, EtaleExpansion.stalkMap_stalkMap_stalkSpecializes_germ]
    rfl
  set t₀ : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) :=
    (XO (ΓM M H) hj ρ).presheaf.germ (U.ι ''ᵁ ⊤) x₀ ⟨⟨x₀, hxU⟩, trivial, rfl⟩ ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X))) - baseGerm ρ x₀ (χQ Polynomial.X) with ht₀_def
  have hembt₀ : emb t₀ = (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ) := by
    rw [ht₀_def, map_sub, hembT, hembC]
  have ht₀O : (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ) ∈ Q.toValuationSubring :=
    hembt₀ ▸ hO t₀
  have hΘt₀ : Θ t₀ = PowerSeries.X := hΘX

  let eR : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) ≃+* ↥emb.range :=
    RingEquiv.ofBijective emb.rangeRestrict ⟨fun a b h => hinj (Subtype.ext_iff.mp h), emb.rangeRestrict_surjective⟩
  have heR' : ∀ g : ↥emb.range, emb (eR.symm g) = (g : ↥(xHFunctionFieldBar M H)) := fun g => by
    have : (eR (eR.symm g) : ↥(xHFunctionFieldBar M H)) = g := by rw [eR.apply_symm_apply]
    exact this
  refine ⟨Θ.comp eR.symm.toRingHom, Θ, ?_, ?_, ?_, ?_, hΘC, hΘfil, hΘsurj⟩
  ·
    intro x hxr
    show Θ (eR.symm ⟨_, hxr⟩) = PowerSeries.C x
    have hb : eR.symm ⟨_, hxr⟩ = baseGerm ρ x₀ x := by
      apply hinj
      rw [heR', hembC]
    rw [hb]
    exact hΘC x
  ·
    intro ht
    show Θ (eR.symm ⟨_, ht⟩) = PowerSeries.X
    have hb : eR.symm ⟨_, ht⟩ = t₀ := by
      apply hinj
      rw [heR', hembt₀]
    rw [hb]
    exact hΘt₀
  ·
    intro g k
    have hgb : emb (eR.symm g) = (g : ↥(xHFunctionFieldBar M H)) := heR' g
    have hΦg : (Θ.comp eR.symm.toRingHom) g = Θ (eR.symm g) := rfl
    have hcoeff : ∀ j : ℕ, j < k → PowerSeries.coeff j (Θ (eR.symm g -
        ∑ i ∈ Finset.range k, baseGerm ρ x₀ (PowerSeries.coeff i (Θ (eR.symm g))) * t₀ ^ i)) = 0 := by
      intro j hjk
      simp only [map_sub, map_sum, map_mul, map_pow, hΘC, hΘt₀, PowerSeries.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq (Finset.range k) j, if_pos (Finset.mem_range.mpr hjk), sub_self]
    have hdk := (hΘfil k _).mp hcoeff
    obtain ⟨r, hr, hrd⟩ := EtaleExpansion.exists_mem_pow_eq_pow_mul Q emb hO _ hK ht₀O hord k _ hdk
    refine ⟨r, hr, ?_⟩
    rw [← hrd]
    simp only [map_sub, map_sum, map_mul, map_pow, hembC, hembt₀, hgb, hΦg]
  ·
    intro b
    show Θ (eR.symm ⟨emb b, b, rfl⟩) = Θ b
    congr 1
    apply hinj
    rw [heR']

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace DiscAux

theorem isOpenImmersion_eeta_prA
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] :
    IsOpenImmersion (𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ)) := by
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  have hgA₁ : (𝔛.eeta ≫ prA) ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _ := by
    rw [Category.assoc, pullback.lift_fst, Category.comp_id]
  have hgA₂ : (𝔛.eeta ≫ prA) ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt A := by
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc, 𝔛.heeta]
  obtain ⟨-, -, hgAoi⟩ :=
    ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
      p M hpM H A hA hj 𝔛 ρ hρ (𝔛.eeta ≫ prA) hgA₁ hgA₂
  exact hgAoi

theorem mkSec
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (u' : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu' : barPt A ≫ u'.1 = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (hκ' : uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫
      pullback.lift u'.1 (𝟙 _) (by rw [u'.2, Category.id_comp])) :
    ∃ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})) (χ : Polynomial ↥A →+* ↥A),
      s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ ∧
      barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ∧
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∧
      s ≫ f = Spec.map (CommRingCat.ofHom χ) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s ≫ U.ι = uκ ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ∧
      s ≫ U.ι = pullback.lift u'.1 (𝟙 _) (by rw [u'.2, Category.id_comp]) := by
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  let x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
  let ut : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ := pullback.lift u'.1 (𝟙 _) (by rw [u'.2, Category.id_comp])
  have hut₁ : ut ≫ pullback.fst _ _ = u'.1 := pullback.lift_fst _ _ _
  have hut₂ : ut ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hx₀ : x₀ = ut.base (IsLocalRing.closedPoint ↥A) := by
    show bcA.base (uκ.base _) = _
    rw [← Scheme.Hom.comp_apply, hκ', Scheme.Hom.comp_apply]
    congr 1
    haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue ↥A)).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue ↥A))
    exact AlgebraicGeometry.Spec_closedPoint
  have hgenW : ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prA = barPt A ≫ ut := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, Category.comp_id, Category.assoc, hut₁, hu']
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc,
        ((𝔛.Meta).pointEquivPlace.symm W).2, Category.id_comp, Category.assoc, hut₂, Category.comp_id]
  have hutU : ut ⁻¹ᵁ U = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff _).mp (show ut.base (IsLocalRing.closedPoint ↥A) ∈ U by rw [← hx₀]; exact hxU)
  have hr : Set.range ut.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show x ∈ ut ⁻¹ᵁ U
    rw [hutU]; trivial
  have hsQ := IsOpenImmersion.lift_fac U.ι ut hr
  have hχ : Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv ≫ (IsOpenImmersion.lift U.ι ut hr ≫ f).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of ↥A)).hom) = IsOpenImmersion.lift U.ι ut hr ≫ f := by
    rw [Spec.map_comp, Spec.map_comp, AlgebraicGeometry.SpecMap_ΓSpecIso_hom,
      ← Scheme.toSpecΓ_naturality, Category.assoc, AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  refine ⟨IsOpenImmersion.lift U.ι ut hr, ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv ≫
    (IsOpenImmersion.lift U.ι ut hr ≫ f).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ↥A)).hom).hom, ?_, ?_, ?_, ?_, ?_, hsQ⟩
  · rw [← Category.assoc, hsQ, hut₂]
  · rw [hsQ]; exact hgenW.symm
  · rw [← Scheme.Hom.comp_apply, hsQ]; exact hx₀.symm
  · rw [CommRingCat.ofHom_hom]; exact hχ.symm
  · rw [hsQ]; exact hκ'.symm

theorem secW
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A))) :
    ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
      ∃ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})) (χ : Polynomial ↥A →+* ↥A),
      s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ ∧
      barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ∧
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∧
      s ≫ f = Spec.map (CommRingCat.ofHom χ) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s ≫ U.ι = uκ ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) := by
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  let x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
  intro W hW hred
  obtain ⟨uW, uκW, P0W, huW, huκW₁, huκW₂, hP0W, hP0WQ, -⟩ :=
    ModularCurve.XHDRModelAtP.exists_section_comp_zero_placeOfPoint_eq_reduceFst_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' W hW
  have hPP : P0W = P0 := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (by rw [hP0WQ, hred, hP0Q])
  have hpt : uκW.base (IsLocalRing.closedPoint (ResidueField ↥A)) = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) := by
    rw [← hP0W, ← hP0, hPP]

  have huκ_eq : uκW = uκ := by
    haveI : IsProper (toBase p (ΓM M H) hj) := 𝔛.isProper
    haveI : LocallyOfFiniteType (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have hinj := (pointEquivClosedPoint (pullback.snd (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))).injective
      (a₁ := ⟨uκW, huκW₂⟩) (a₂ := ⟨uκ, huκ₂⟩) (Subtype.ext hpt)
    exact congrArg Subtype.val hinj
  rw [huκ_eq] at huκW₁ huκW₂
  have hκW : uκ ≫ bcA = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ pullback.lift uW.1 (𝟙 _) (by rw [uW.2, Category.id_comp]) := by
    show uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl = _
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, huκW₁, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, bcMap_snd, ← Category.assoc, huκW₂, Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
  obtain ⟨s, χ, h1, h2, h3, h4, h5, -⟩ := DiscAux.mkSec p M H hpM hj 𝔛 A ρ hρ uκ U hxU f W uW huW hκW
  exact ⟨s, χ, h1, h2, h3, h4, h5⟩

theorem param_mem_integers
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)
    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) :
    (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) ∈ Rpd.R₁.integers := by
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  let x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
  have hxW' : x₀ ∈ (U.ι ''ᵁ ⊤ : (XO (ΓM M H) hj ρ).Opens) := by rw [Scheme.Opens.ι_image_top]; exact hxU
  have hξ : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ⤳ x₀ := by
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    have e : x₀ = (𝔛.comp A hA ρ hρ 0 ≫ bcA).base ((𝔛.efib A hA ρ hρ).base P0.1) := by
      show bcA.base (uκ.base _) = _
      rw [← hP0, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [e]
    show (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base (genericPoint (𝔛.Mfib A hA ρ hρ).C) ⤳ _
    rw [Scheme.Hom.comp_apply]
    exact (𝔛.efib_genericPoint_specializes A hA ρ hρ ((𝔛.efib A hA ρ hρ).base P0.1)).map
      (𝔛.comp A hA ρ hρ 0 ≫ bcA).base.hom.continuous
  have hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ (U.ι ''ᵁ ⊤ : (XO (ΓM M H) hj ρ).Opens) :=
    hξ.mem_open (U.ι ''ᵁ ⊤).isOpen hxW'
  obtain ⟨h₁, -⟩ := (ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
    θ Psp Rpd hwgen (U.ι ''ᵁ ⊤) hgen ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))).1 hi
  exact h₁

end DiscAux

set_option maxHeartbeats 6400000 in
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ (hsp : prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀),
    letI emb : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))
    ∃ (t : ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A) (Φ : ↥(emb.range) →+* PowerSeries ↥A),

        t ∈ Rpd.R₁.integers ∧
        (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
          c W ∈ maximalIdeal ↥A ∧ W.ord (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1) ∧
        (∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Q →
          c W = c W' → W = W') ∧

        (∀ (x : ↥A) (hx : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (x : AlgebraicClosure ℚ) ∈ emb.range), Φ ⟨_, hx⟩ = PowerSeries.C x) ∧
        (∀ ht : t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ emb.range, Φ ⟨_, ht⟩ = PowerSeries.X) ∧

        (∀ (f : ↥(emb.range)) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (f : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ f) : ↥A) : AlgebraicClosure ℚ) *
              (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            (t - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) ∧

        (∀ (f : ↥(emb.range)) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ f) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A →
          Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 ∧
            (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
        (∀ (f : ↥(emb.range)) (hf : (f : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ f) ∉ maximalIdeal ↥A) := by
  intro hsp
  classical

  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XO (ΓM M H) hj ρ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  let x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))

  haveI : IsOpenImmersion (𝔛.eeta ≫ prA) := DiscAux.isOpenImmersion_eeta_prA p M H hpM hj 𝔛 A ρ hρ hA

  obtain ⟨U, hxU, f, hover, het, hpt⟩ := ModularCurve.XHDRModelAtP.exists_etale_chart_affineLine_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsmooth
  have hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤)) := by
    have hxW' : x₀ ∈ (U.ι ''ᵁ ⊤ : (XO (ΓM M H) hj ρ).Opens) := by rw [Scheme.Opens.ι_image_top]; exact hxU
    exact hsp.mem_open (U.ι ''ᵁ ⊤).isOpen hxW'

  have hκQ : uκ ≫ bcA = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp]) := by
    show uκ ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl = _
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst, huκ₁, Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, bcMap_snd, ← Category.assoc, huκ₂, Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
  obtain ⟨sQ, χQ, hsQover, hsQgen, hsQpt, hsQf, hsQκ, hsQut⟩ := DiscAux.mkSec p M H hpM hj 𝔛 A ρ hρ uκ U hxU f Q u hu hκQ

  have hxQ : (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp]) : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ).base
      (IsLocalRing.closedPoint ↥A) = x₀ := by
    rw [← hsQut, Scheme.Hom.comp_apply]; exact hsQpt

  have secW : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
      ∃ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})) (χ : Polynomial ↥A →+* ↥A),
      s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ ∧
      barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ∧
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))) ∧
      s ≫ f = Spec.map (CommRingCat.ofHom χ) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s ≫ U.ι = uκ ≫ (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) :=
    DiscAux.secW p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsmooth U hxU f

  let sW : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W →
      Psp.reduceFst α hα W = Psp.reduceFst α hα Q → (Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})) :=
    fun W hW hred => if h : W = Q then sQ else (secW W hW hred).choose
  let χW : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W →
      Psp.reduceFst α hα W = Psp.reduceFst α hα Q → (Polynomial ↥A →+* ↥A) :=
    fun W hW hred => if h : W = Q then χQ else (secW W hW hred).choose_spec.choose
  have hsWall : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hW : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W)
      (hred : Psp.reduceFst α hα W = Psp.reduceFst α hα Q),
      sW W hW hred ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ ∧
      barPt A ≫ sW W hW hred ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prA ∧
      U.ι.base ((sW W hW hred).base (IsLocalRing.closedPoint ↥A)) = x₀ ∧
      sW W hW hred ≫ f = Spec.map (CommRingCat.ofHom (χW W hW hred)) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ sW W hW hred ≫ U.ι = uκ ≫ bcA := by
    intro W hW hred
    by_cases h : W = Q
    · subst h
      simp only [sW, χW, dif_pos rfl]
      exact ⟨hsQover, hsQgen, hsQpt, hsQf, hsQκ⟩
    · simp only [sW, χW, dif_neg h]
      exact (secW W hW hred).choose_spec.choose_spec
  have hsWover := fun W hW hred => (hsWall W hW hred).1
  have hsWgen := fun W hW hred => (hsWall W hW hred).2.1
  have hsWpt := fun W hW hred => (hsWall W hW hred).2.2.1
  have hsWf := fun W hW hred => (hsWall W hW hred).2.2.2.1
  have hsWκ := fun W hW hred => (hsWall W hW hred).2.2.2.2
  have hχWQ : χW Q hQ rfl = χQ := by simp only [χW, dif_pos rfl]

  have keyB1 := ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsmooth U hxU f hover het hpt hgen
  have hrat : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.IsRational := by
    intro W
    have := AlgebraicCurve.CurveModel.isRational_pointEquivPlace (𝔛.Meta) ((𝔛.Meta).pointEquivPlace.symm W)
    rwa [Equiv.apply_symm_apply] at this
  let c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ↥A := fun W =>
    if h : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ Psp.reduceFst α hα W = Psp.reduceFst α hα Q then χW W h.1 h.2 Polynomial.X else 0
  have hc : ∀ W (hW : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W) (hred : Psp.reduceFst α hα W = Psp.reduceFst α hα Q), c W = χW W hW hred Polynomial.X := by
    intro W hW hred; simp only [c, dif_pos (And.intro hW hred)]
  have hP2 : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q →
      c W ∈ maximalIdeal ↥A ∧ W.ord ((((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c W : AlgebraicClosure ℚ)) = 1 := by
    intro W hW hred
    obtain ⟨h1, -, -, h4⟩ := keyB1 W (hrat W) (sW W hW hred) (hsWover W hW hred) (hsWgen W hW hred) (hsWpt W hW hred) (χW W hW hred) (hsWf W hW hred)
    rw [hc W hW hred]
    exact ⟨h1, h4⟩

  have keyA2 := ModularCurve.XHDRModelAtP.section_eq_of_specMap_residue_comp_eq_of_comp_etale_chart_eq_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsmooth U hxU f hover het hpt
  have hP3 : ∀ W W' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W' → Psp.reduceFst α hα W' = Psp.reduceFst α hα Q →
      c W = c W' → W = W' := by
    intro W W' hW hred hW' hred' hcc
    rw [hc W hW hred, hc W' hW' hred'] at hcc
    have hχ : χW W hW hred = χW W' hW' hred' := by
      have hC : ∀ (W₁ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
          (h₁ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W₁) (h₂ : Psp.reduceFst α hα W₁ = Psp.reduceFst α hα Q),
          (χW W₁ h₁ h₂).comp Polynomial.C = RingHom.id ↥A := by
        intro W₁ h₁ h₂
        have h : Spec.map (CommRingCat.ofHom (χW W₁ h₁ h₂)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = 𝟙 _ := by
          rw [← hsWf W₁ h₁ h₂, Category.assoc, hover, hsWover W₁ h₁ h₂]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id] at h
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
      apply Polynomial.ringHom_ext
      · intro a
        have e1 := DFunLike.congr_fun (hC W hW hred) a
        have e2 := DFunLike.congr_fun (hC W' hW' hred') a
        simp only [RingHom.comp_apply, RingHom.id_apply] at e1 e2
        rw [e1, e2]
      · exact hcc
    have hκ : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ sW W hW hred =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ sW W' hW' hred' := by
      have h2 := (hsWκ W hW hred).trans (hsWκ W' hW' hred').symm
      rw [← Category.assoc, ← Category.assoc] at h2
      exact (cancel_mono U.ι).mp h2
    have hs : sW W hW hred = sW W' hW' hred' := keyA2 _ _ (hsWover W hW hred) (hsWover W' hW' hred') hκ
      (by rw [hsWf W hW hred, hsWf W' hW' hred', hχ])
    have e := hsWgen W hW hred
    rw [hs] at e
    have hgen_eq := e.symm.trans (hsWgen W' hW' hred')
    have h1 : ((𝔛.Meta).pointEquivPlace.symm W).1 = ((𝔛.Meta).pointEquivPlace.symm W').1 :=
      (cancel_mono (𝔛.eeta ≫ prA)).mp hgen_eq
    exact (𝔛.Meta).pointEquivPlace.symm.injective (Subtype.ext h1)

  have hP1 : (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) ∈ Rpd.R₁.integers :=
    DiscAux.param_mem_integers p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsmooth U hxU f hgen

  have hkeyQ := keyB1 Q (hrat Q) sQ hsQover hsQgen hsQpt χQ hsQf
  obtain ⟨Φ, Θ, hΦC, hΦX₀, hT₀, hΦΘ, hΘC, hΘfil, hΘsurj⟩ :=
    EtaleExpansion.expan_of_etaleChart p M H hpM hj 𝔛 A hA ρ hρ x₀ prA rfl hsp U hxU f hover het hgen Q sQ χQ hsQover hsQgen hsQf
      (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])) hsQut hxQ hkeyQ.2.1 hkeyQ.2.2.2
  have hcQ : ((c Q : ↥A) : AlgebraicClosure ℚ) = ((χQ Polynomial.X : ↥A) : AlgebraicClosure ℚ) := by rw [hc Q hQ rfl, hχWQ]
  have hΦX : (∀ ht : (((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ) ∈ ((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range, Φ ⟨_, ht⟩ = PowerSeries.X) := by
    rw [hcQ]; exact hΦX₀
  have hT : (∀ (g : ↥(((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range)) (k : ℕ), ∃ r ∈ Q.toValuationSubring,
          (g : ↥(xHFunctionFieldBar M H)) - ∑ i ∈ Finset.range k, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((PowerSeries.coeff i (Φ g) : ↥A) : AlgebraicClosure ℚ) *
              ((((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ i =
            ((((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ) ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).app (U.ι ''ᵁ ⊤)).hom))) ((U.ι.appIso ⊤).inv (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom Polynomial.X)))) - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c Q : AlgebraicClosure ℚ)) ^ k * r) := by
    rw [hcQ]; exact hT₀

  have hR : (∀ (g : ↥(((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range)) (hg : (g : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers) (k : ℕ),
          (∀ i < k, PowerSeries.coeff i (Φ g) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Φ g) ∉ maximalIdeal ↥A →
          Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 ∧
            (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨g, hg⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
        (∀ (g : ↥(((𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          (((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]) :
        pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρ).stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))).range)) (hg : (g : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg⟩ ≠ 0 →
          ∃ k, PowerSeries.coeff k (Φ g) ∉ maximalIdeal ↥A) := by
    have RO := fun b hb => ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' Q hQ u uκ P0 hu huκ₁ huκ₂ hP0 hP0Q hsmooth hsp hxQ Θ hΘC hΘfil hΘsurj b hb
    constructor
    · intro g hg k hlow hhigh
      obtain ⟨b, hb⟩ := g.2
      have hg' : g = ⟨_, ⟨b, rfl⟩⟩ := Subtype.ext hb.symm
      subst hg'
      rw [hΦΘ b] at hlow hhigh
      exact (RO b hg).1 k hlow hhigh
    · intro g hg hres
      obtain ⟨b, hb⟩ := g.2
      have hg' : g = ⟨_, ⟨b, rfl⟩⟩ := Subtype.ext hb.symm
      subst hg'
      obtain ⟨k, hk⟩ := (RO b hg).2 hres
      exact ⟨k, by rw [hΦΘ b]; exact hk⟩
  exact ⟨_, c, Φ, hP1, hP2, hP3, hΦC, hΦX, hT, hR.1, hR.2⟩

end S_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst (solution)
