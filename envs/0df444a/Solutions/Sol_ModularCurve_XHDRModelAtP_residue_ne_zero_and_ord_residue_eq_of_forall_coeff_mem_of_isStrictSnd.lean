-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3d03bf95-85a7-5345-bae8-e9a88e111791

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff
import Theorems.Thm_ModularCurve_XHDRModelAtP_readA_mem_integers_and_residue_eq_restrict_comp_of_mem
import Theorems.Thm_AlgebraicGeometry_isIso_stalkMap_of_isClosedImmersion_of_not_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

universe u v

open TopologicalSpace Topology

namespace ResidueOrdAux

theorem ker_comp_eq_ker_sup_map {O A κ : Type*} [CommRing O] [CommRing A] [CommRing κ]
    (χ : O →+* A) (σ : A →+* O) (hσ : ∀ a, χ (σ a) = a) (r : A →+* κ) :
    RingHom.ker (r.comp χ) = RingHom.ker χ ⊔ (RingHom.ker r).map σ := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply] at hx
    have h1 : x - σ (χ x) ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker, map_sub, hσ, sub_self]
    have h2 : σ (χ x) ∈ (RingHom.ker r).map σ := Ideal.mem_map_of_mem _ (by rwa [RingHom.mem_ker])
    simpa using Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
  · refine sup_le (fun x hx => ?_) ?_
    · rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, hx, map_zero]
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [RingHom.mem_ker] at ha
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hσ, ha]

theorem map_eq_maximalIdeal_of_sup_eq {O D : Type*} [CommRing O] [CommRing D] [IsLocalRing O] [IsLocalRing D]
    (lam : O →+* D) (hlam : Function.Surjective lam) (I J : Ideal O) (hJ : J ≤ RingHom.ker lam)
    (hIJ : I ⊔ J = maximalIdeal O) : I.map lam = maximalIdeal D := by
  have h : (I ⊔ J).map lam = I.map lam := by
    rw [Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker lam).mpr hJ, sup_bot_eq]
  rw [← h, hIJ, IsLocalRing.map_maximalIdeal_of_surjective lam hlam]

theorem mem_pow_sup_iff_map_mem_pow {O D : Type*} [CommRing O] [CommRing D]
    (lam : O →+* D) (hlam : Function.Surjective lam) (I J : Ideal O) (𝔫 : Ideal D)
    (hJ : J ≤ RingHom.ker lam) (hker : RingHom.ker lam ≤ J) (hI : I.map lam = 𝔫) (k : ℕ) (b : O) :
    b ∈ I ^ k ⊔ J ↔ lam b ∈ 𝔫 ^ k := by
  have hmap : (I ^ k ⊔ J).map lam = 𝔫 ^ k := by
    rw [Ideal.map_sup, Ideal.map_pow, hI, (Ideal.map_eq_bot_iff_le_ker lam).mpr hJ, sup_bot_eq]
  constructor
  · intro hb
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hb
  · intro hb
    have : b ∈ (𝔫 ^ k).comap lam := hb
    rw [← hmap, Ideal.comap_map_of_surjective _ hlam] at this
    rcases Submodule.mem_sup.mp this with ⟨y, hy, z, hz, rfl⟩
    have hz' : z ∈ J := hker (by simpa [Ideal.mem_comap] using hz)
    exact Ideal.add_mem _ hy (Ideal.mem_sup_right hz')

theorem map_mem_pow_of_mem_pow_sup {O D : Type*} [CommRing O] [CommRing D]
    (lam : O →+* D) (I J : Ideal O) (𝔫 : Ideal D)
    (hJ : J ≤ RingHom.ker lam) (hI : I.map lam = 𝔫) (k : ℕ) (b : O) (hb : b ∈ I ^ k ⊔ J) :
    lam b ∈ 𝔫 ^ k := by
  have hmap : (I ^ k ⊔ J).map lam = 𝔫 ^ k := by
    rw [Ideal.map_sup, Ideal.map_pow, hI, (Ideal.map_eq_bot_iff_le_ker lam).mpr hJ, sup_bot_eq]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hb

theorem exists_eq_unit_mul_pow_of_mem_pow_of_not_mem {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (k : ℕ) (e : R) (hk : e ∈ maximalIdeal R ^ k) (hk' : e ∉ maximalIdeal R ^ (k + 1)) :
    ∃ u : Rˣ, e = u * ϖ ^ k := by
  have he : e ≠ 0 := by rintro rfl; exact hk' (Ideal.zero_mem _)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible he hϖ
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hk hk'
  have h1 : k ≤ n := by
    have : ϖ ^ k ∣ ϖ ^ n := (Units.dvd_mul_left).mp hk
    exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp this
  have h2 : n ≤ k := by
    by_contra h
    exact hk' ((Units.dvd_mul_left).mpr (pow_dvd_pow ϖ (by omega)))
  obtain rfl : n = k := le_antisymm h2 h1
  exact ⟨u, rfl⟩

theorem CurveModel.read_ne_zero_and_ord_eq {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (Mc : AlgebraicCurve.CurveModel K L) (x : closedPoints Mc.C) (k : ℕ) (d : Mc.C.presheaf.stalk x.1)
    (hk : d ∈ maximalIdeal (Mc.C.presheaf.stalk x.1) ^ k) (hk' : d ∉ maximalIdeal (Mc.C.presheaf.stalk x.1) ^ (k + 1)) :
    Mc.ffEquiv.symm (algebraMap (Mc.C.presheaf.stalk x.1) Mc.C.functionField d) ≠ 0 ∧
      (Mc.placeOfPoint x).ord (Mc.ffEquiv.symm (algebraMap (Mc.C.presheaf.stalk x.1) Mc.C.functionField d)) = k := by
  classical
  set v := Mc.placeOfPoint x
  let read : Mc.C.presheaf.stalk x.1 →+* L :=
    (Mc.ffEquiv.symm : Mc.C.functionField ≃+* L).toRingHom.comp (algebraMap (Mc.C.presheaf.stalk x.1) Mc.C.functionField)
  have hread_inj : Function.Injective read :=
    Mc.ffEquiv.symm.injective.comp (IsFractionRing.injective (Mc.C.presheaf.stalk x.1) Mc.C.functionField)
  have hrange : read.range = v.toValuationSubring.toSubring := Mc.range_stalk_eq x
  have hmem : ∀ o, read o ∈ v.toValuationSubring.toSubring := fun o => hrange ▸ ⟨o, rfl⟩
  let r' : Mc.C.presheaf.stalk x.1 →+* v.toValuationSubring := read.codRestrict v.toValuationSubring.toSubring hmem
  have hr'_inj : Function.Injective r' := fun a b h => hread_inj (congrArg Subtype.val h)
  have hr'_surj : Function.Surjective r' := by
    rintro ⟨y, hy⟩
    have : y ∈ read.range := hrange ▸ hy
    obtain ⟨o, rfl⟩ := this
    exact ⟨o, rfl⟩
  let e : Mc.C.presheaf.stalk x.1 ≃+* v.toValuationSubring := RingEquiv.ofBijective r' ⟨hr'_inj, hr'_surj⟩
  have hmax : (maximalIdeal (Mc.C.presheaf.stalk x.1)).map (e : Mc.C.presheaf.stalk x.1 →+* v.toValuationSubring) =
      maximalIdeal v.toValuationSubring := IsLocalRing.map_ringEquiv_maximalIdeal e
  have hk1 : e d ∈ maximalIdeal v.toValuationSubring ^ k := by
    rw [← hmax, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hk
  have hk2 : e d ∉ maximalIdeal v.toValuationSubring ^ (k + 1) := by
    rw [← hmax, ← Ideal.map_pow]
    intro h
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at h
    exact hk' (by simpa using h)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨w, hw⟩ := exists_eq_unit_mul_pow_of_mem_pow_of_not_mem hϖ k (e d) hk1 hk2
  have hcoe : Mc.ffEquiv.symm (algebraMap (Mc.C.presheaf.stalk x.1) Mc.C.functionField d) = ((e d : v.toValuationSubring) : L) := rfl
  rw [hcoe, hw]
  refine ⟨?_, ?_⟩
  · have : (w : v.toValuationSubring) * ϖ ^ k ≠ 0 := mul_ne_zero w.ne_zero (pow_ne_zero _ hϖ.ne_zero)
    exact fun h => this (Subtype.ext (by simpa using h))
  · have := v.ord_unit_smul_zpow w hϖ (k : ℤ)
    rw [zpow_natCast] at this
    simpa using this

theorem CurveModel.exists_not_mem_pow_of_read_ne_zero {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (Mc : AlgebraicCurve.CurveModel K L) (x : closedPoints Mc.C) (d : Mc.C.presheaf.stalk x.1)
    (hd : Mc.ffEquiv.symm (algebraMap (Mc.C.presheaf.stalk x.1) Mc.C.functionField d) ≠ 0) :
    ∃ k : ℕ, d ∉ maximalIdeal (Mc.C.presheaf.stalk x.1) ^ (k + 1) := by
  classical
  set v := Mc.placeOfPoint x
  let read : Mc.C.presheaf.stalk x.1 →+* L :=
    (Mc.ffEquiv.symm : Mc.C.functionField ≃+* L).toRingHom.comp (algebraMap (Mc.C.presheaf.stalk x.1) Mc.C.functionField)
  have hread_inj : Function.Injective read :=
    Mc.ffEquiv.symm.injective.comp (IsFractionRing.injective (Mc.C.presheaf.stalk x.1) Mc.C.functionField)
  have hrange : read.range = v.toValuationSubring.toSubring := Mc.range_stalk_eq x
  have hmem : ∀ o, read o ∈ v.toValuationSubring.toSubring := fun o => hrange ▸ ⟨o, rfl⟩
  let r' : Mc.C.presheaf.stalk x.1 →+* v.toValuationSubring := read.codRestrict v.toValuationSubring.toSubring hmem
  have hr'_inj : Function.Injective r' := fun a b h => hread_inj (congrArg Subtype.val h)
  have hr'_surj : Function.Surjective r' := by
    rintro ⟨y, hy⟩
    have : y ∈ read.range := hrange ▸ hy
    obtain ⟨o, rfl⟩ := this
    exact ⟨o, rfl⟩
  let e : Mc.C.presheaf.stalk x.1 ≃+* v.toValuationSubring := RingEquiv.ofBijective r' ⟨hr'_inj, hr'_surj⟩
  have hmax : (maximalIdeal (Mc.C.presheaf.stalk x.1)).map (e : Mc.C.presheaf.stalk x.1 →+* v.toValuationSubring) =
      maximalIdeal v.toValuationSubring := IsLocalRing.map_ringEquiv_maximalIdeal e
  have he : e d ≠ 0 := by
    intro h
    apply hd
    have : ((e d : v.toValuationSubring) : L) = 0 := by rw [h]; rfl
    exact this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible he hϖ
  refine ⟨n, fun hmemd => ?_⟩
  have : e d ∈ maximalIdeal v.toValuationSubring ^ (n + 1) := by
    rw [← hmax, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hmemd
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hw] at this
  have h1 : ϖ ^ (n + 1) ∣ ϖ ^ n := (Units.dvd_mul_left).mp this
  have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h1
  omega

theorem main_reduction_law {A O D L : Type*} [CommRing A] [IsLocalRing A] [CommRing O] [IsLocalRing O] [CommRing D] [IsLocalRing D]
    (χ : O →+* A) (σ : A →+* O) (hχσ : ∀ a, χ (σ a) = a)
    (Θ : O →+* PowerSeries A)
    (hE : ∀ (n : ℕ) (a : O), (∀ k : ℕ, k < n → PowerSeries.coeff k (Θ a) ∈ maximalIdeal A) ↔
      a ∈ RingHom.ker χ ^ n ⊔ (maximalIdeal A).map σ)
    (lam : O →+* D) (hsurj : Function.Surjective lam)
    (hJker : (maximalIdeal A).map σ ≤ RingHom.ker lam) (hkerJ : RingHom.ker lam ≤ (maximalIdeal A).map σ)
    (rd : D → L) [Zero L] (ordv : L → ℤ)
    (hGD : ∀ (k : ℕ) (d : D), d ∈ maximalIdeal D ^ k → d ∉ maximalIdeal D ^ (k + 1) → rd d ≠ 0 ∧ ordv (rd d) = k)
    (hGD2 : ∀ d : D, rd d ≠ 0 → ∃ k : ℕ, d ∉ maximalIdeal D ^ (k + 1))
    (b : O) :
    (∀ k : ℕ, (∀ i < k, PowerSeries.coeff i (Θ b) ∈ maximalIdeal A) → PowerSeries.coeff k (Θ b) ∉ maximalIdeal A →
        rd (lam b) ≠ 0 ∧ ordv (rd (lam b)) = k) ∧
      (rd (lam b) ≠ 0 → ∃ k : ℕ, PowerSeries.coeff k (Θ b) ∉ maximalIdeal A) := by
  classical

  have hIJ : RingHom.ker χ ⊔ (maximalIdeal A).map σ = maximalIdeal O := by
    have h := ker_comp_eq_ker_sup_map χ σ hχσ (IsLocalRing.residue A)
    rw [IsLocalRing.ker_residue] at h
    rw [← h]
    refine IsLocalRing.ker_eq_maximalIdeal _ (fun t => ?_)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective t
    exact ⟨σ a, by rw [RingHom.comp_apply, hχσ]⟩
  have hI : (RingHom.ker χ).map lam = maximalIdeal D :=
    map_eq_maximalIdeal_of_sup_eq lam hsurj _ _ hJker hIJ
  have hmain : ∀ k : ℕ, b ∈ RingHom.ker χ ^ k ⊔ (maximalIdeal A).map σ ↔ lam b ∈ maximalIdeal D ^ k := fun k =>
    mem_pow_sup_iff_map_mem_pow lam hsurj _ _ _ hJker hkerJ hI k b
  refine ⟨fun k hlt hk => ?_, fun hres => ?_⟩
  · have h1 : lam b ∈ maximalIdeal D ^ k := (hmain k).mp ((hE k b).mp hlt)
    have h2 : lam b ∉ maximalIdeal D ^ (k + 1) := fun h => by
      have := (hE (k + 1) b).mpr ((hmain (k + 1)).mpr h)
      exact hk (this k (Nat.lt_succ_self k))
    exact hGD k (lam b) h1 h2
  · obtain ⟨k, hk⟩ := hGD2 (lam b) hres
    have : ¬ ∀ i : ℕ, i < k + 1 → PowerSeries.coeff i (Θ b) ∈ maximalIdeal A := fun h =>
      hk ((hmain (k + 1)).mp ((hE (k + 1) b).mp h))
    push Not at this
    obtain ⟨i, -, hi⟩ := this
    exact ⟨i, hi⟩

end ResidueOrdAux

namespace ResidueOrdAux

theorem mem_map_of_app_eq_zero_of_isPullback {O : Type u} [CommRing O] (𝔞 : Ideal O)
    {Z Zκ : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of O)) (j : Zκ ⟶ Z) (q : Zκ ⟶ Spec (CommRingCat.of (O ⧸ 𝔞)))
    (H : IsPullback j q g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))))
    {V : Z.Opens} (hV : IsAffineOpen V) (f : Γ(Z, V)) (hf : (j.app V).hom f = 0) :
    f ∈ 𝔞.map ((g.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := by
  classical
  set φ : O →+* Γ(Z, V) := (g.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom with hφ
  set 𝔟 : Ideal Γ(Z, V) := 𝔞.map φ with h𝔟
  have hle : 𝔞 ≤ 𝔟.comap φ := Ideal.le_comap_map
  let ψ : O ⧸ 𝔞 →+* Γ(Z, V) ⧸ 𝔟 := Ideal.quotientMap 𝔟 φ hle
  let Q : CommRingCat.{u} := CommRingCat.of (Γ(Z, V) ⧸ 𝔟)
  let mk' : Γ(Z, V) ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk 𝔟)

  let m : Spec Q ⟶ Z := Spec.map mk' ≫ hV.fromSpec
  have hφ' : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appLE ⊤ V le_top := rfl
  have hVg : hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom φ) := by
    rw [hφ', Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top]
  have comm : m ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)) := by
    rw [Category.assoc, hVg, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let w := H.lift m (Spec.map (CommRingCat.ofHom ψ)) comm
  have hw : w ≫ j = m := H.lift_fst _ _ _
  have hmV : (⊤ : (Spec Q).Opens) ≤ m ⁻¹ᵁ V := by
    rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
    exact le_rfl

  have key : ∀ (m' : Spec Q ⟶ Z) (h' : (⊤ : (Spec Q).Opens) ≤ m' ⁻¹ᵁ V), m' = w ≫ j → (m'.appLE V ⊤ h').hom f = 0 := by
    rintro _ h' rfl
    rw [← Scheme.Hom.appLE_comp_appLE w j V (j ⁻¹ᵁ V) ⊤ le_rfl h', CommRingCat.comp_apply,
      Scheme.Hom.appLE_eq_app, hf, map_zero]
  have h1 : (m.appLE V ⊤ hmV).hom f = 0 := key m hmV hw.symm

  have h2 : m.appLE V ⊤ hmV ≫ (Scheme.ΓSpecIso Q).hom = mk' := by
    have e1 : m.appLE V ⊤ hmV = hV.fromSpec.appLE V ⊤ (by rw [IsAffineOpen.fromSpec_preimage_self]) ≫
        (Spec.map mk').appTop := by
      have := Scheme.Hom.appLE_comp_appLE (Spec.map mk') hV.fromSpec V ⊤ (Spec.map mk' ⁻¹ᵁ ⊤)
        (by rw [IsAffineOpen.fromSpec_preimage_self]) le_rfl
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact this.symm
    have e2 : hV.fromSpec.appLE V ⊤ (by rw [IsAffineOpen.fromSpec_preimage_self]) =
        (Scheme.ΓSpecIso Γ(Z, V)).inv := by
      rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      convert Category.comp_id _
      all_goals first | rfl | (exact (congrArg (fun f => (Spec Γ(Z, V)).presheaf.map f) (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _))
    rw [e1, e2, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h3 : Ideal.Quotient.mk 𝔟 f = 0 := by
    have := congrArg (fun t => (Scheme.ΓSpecIso Q).hom.hom t) h1
    simp only [map_zero] at this
    rw [← CommRingCat.comp_apply, h2] at this
    exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

theorem ker_stalkMap_le_map_of_isPullback {O : Type u} [CommRing O] (𝔞 : Ideal O)
    {Z Zκ : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of O)) (j : Zκ ⟶ Z) (q : Zκ ⟶ Spec (CommRingCat.of (O ⧸ 𝔞)))
    (H : IsPullback j q g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞)))) (c : Zκ) :
    RingHom.ker (j.stalkMap c).hom ≤
      𝔞.map ((Z.presheaf.germ ⊤ (j.base c) trivial).hom.comp (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) := by
  classical
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔞))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion j := MorphismProperty.of_isPullback H.flip inferInstance
  intro s hs
  rw [RingHom.mem_ker] at hs
  obtain ⟨U, hxU, f, rfl⟩ := Z.presheaf.exists_germ_eq s
  rw [Scheme.Hom.germ_stalkMap_apply] at hs

  obtain ⟨W', hcW', iU, iV, hW'⟩ := Zκ.presheaf.germ_eq (U := j ⁻¹ᵁ U) (V := j ⁻¹ᵁ U) c hxU hxU ((j.app U).hom f) 0
    (by rw [hs, map_zero])
  rw [map_zero] at hW'

  obtain ⟨V₀, hV₀, hV₀eq⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.mp W'.2
  have hcV₀ : j.base c ∈ V₀ := by
    have : c ∈ j.base ⁻¹' V₀ := by rw [hV₀eq]; exact hcW'
    exact this

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVsub⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (show j.base c ∈ (U : Set Z) ∩ V₀ from ⟨hxU, hcV₀⟩) (U.2.inter hV₀)
  have hVU : V ≤ U := fun z hz => (hVsub hz).1
  have hjV : j ⁻¹ᵁ V ≤ W' := fun z hz => by
    have : z ∈ j.base ⁻¹' V₀ := (hVsub hz).2
    rw [hV₀eq] at this
    exact this
  rw [← Z.presheaf.germ_res_apply (homOfLE hVU) (j.base c) hxV f]

  have hfV : (j.app V).hom ((Z.presheaf.map (homOfLE hVU).op).hom f) = 0 := by
    have nat := j.naturality (homOfLE hVU).op
    rw [← CommRingCat.comp_apply, nat, CommRingCat.comp_apply]
    have hfac : ((TopologicalSpace.Opens.map j.base).map (homOfLE hVU).op.unop).op = iU.op ≫ (homOfLE hjV).op :=
      Subsingleton.elim _ _
    rw [hfac, Functor.map_comp, CommRingCat.comp_apply, hW', map_zero]
  have hmem := mem_map_of_app_eq_zero_of_isPullback 𝔞 g j q H hV _ hfV
  have hσ : (Z.presheaf.germ V (j.base c) hxV).hom.comp
      ((g.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) =
      (Z.presheaf.germ ⊤ (j.base c) trivial).hom.comp (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := by
    refine RingHom.ext fun o => ?_
    simp only [RingHom.comp_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
    exact Z.presheaf.germ_res_apply _ _ _ _
  rw [← hσ, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hmem

end ResidueOrdAux

namespace ResidueOrdAux

theorem app_top_apply_of_comp_eq {C X S T : Scheme.{u}} (ι : C ⟶ X) (g : X ⟶ S) (t : C ⟶ T) (r : T ⟶ S)
    (h : ι ≫ g = t ≫ r) (s : Γ(S, ⊤)) :
    (ι.app ⊤).hom (g.appTop.hom s) = t.appTop.hom (r.appTop.hom s) := by
  change (g.appTop ≫ ι.appTop).hom s = (r.appTop ≫ t.appTop).hom s
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h]

theorem specMap_appTop_ΓSpecIso_inv_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (a : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) = (Scheme.ΓSpecIso S).inv.hom (f.hom a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

theorem stalkMap_comp₃_apply {C F X Y : Scheme.{u}} (e : C ⟶ F) (c : F ⟶ X) (j : X ⟶ Y) (x : C)
    (s : Y.presheaf.stalk ((e ≫ c ≫ j).base x)) :
    ((e ≫ c ≫ j).stalkMap x).hom s = (e.stalkMap x).hom ((c.stalkMap (e.base x)).hom ((j.stalkMap (c.base (e.base x))).hom s)) := by
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
  rfl

theorem eq_zero_of_isIso_apply {R S : CommRingCat.{u}} (f : R ⟶ S) [IsIso f] (s : R) (h : f.hom s = 0) : s = 0 :=
  (injective_iff_map_eq_zero f.hom).mp (ConcreteCategory.bijective_of_isIso f).1 s h

theorem stalkMap_stalkMap_stalkSpecializes_germ {MC XQ XA : Scheme.{u}} (eeta : MC ⟶ XQ) (prA : XQ ⟶ XA) (η : MC)
    {x : XA} (hsp : prA.base (eeta.base η) ⤳ x) (V : XA.Opens) (hx : x ∈ V) (g : Γ(XA, V)) :
    (eeta.stalkMap η).hom ((prA.stalkMap (eeta.base η)).hom ((XA.presheaf.stalkSpecializes hsp).hom ((XA.presheaf.germ V x hx).hom g))) =
      (MC.presheaf.germ (eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) η (hsp.mem_open V.2 hx)).hom ((eeta.app (prA ⁻¹ᵁ V)).hom ((prA.app V).hom g)) := by
  rw [← CommRingCat.comp_apply (XA.presheaf.germ V x hx), TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply]

theorem stalkSpecializes_stalkMap_germ {C XA : Scheme.{u}} (ι : C ⟶ XA) (P η : C) (hη : η ⤳ P) (V : XA.Opens)
    (hP : ι.base P ∈ V) (g : Γ(XA, V)) :
    (C.presheaf.stalkSpecializes hη).hom ((ι.stalkMap P).hom ((XA.presheaf.germ V (ι.base P) hP).hom g)) =
      (C.presheaf.germ (ι ⁻¹ᵁ V) η (hη.mem_open (ι ⁻¹ᵁ V).2 hP)).hom ((ι.app V).hom g) := by
  rw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

end ResidueOrdAux

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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base) :
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

    letI ut : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ := pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])
    ∀ (hx : ut.base (IsLocalRing.closedPoint ↥A) = x₀),
    letI χ : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥A :=
      (Scheme.stalkClosedPointTo ut).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom

    ∀ (Θ : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* PowerSeries ↥A),
      (∀ a : ↥A, Θ (baseGerm ρ x₀ a) = PowerSeries.C a) →
      (∀ (n : ℕ) (b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀)),
        (∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = 0) ↔ b ∈ RingHom.ker χ ^ n) →
      (∀ (n : ℕ) (q : PowerSeries ↥A), ∃ b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀),
        ∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = PowerSeries.coeff k q) →

    ∀ (b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀)) (hb : emb b ∈ Rpd.R₂.integers),
      (∀ k : ℕ, (∀ i < k, PowerSeries.coeff i (Θ b) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Θ b) ∉ maximalIdeal ↥A →
        Rpd.R₂.residue ⟨emb b, hb⟩ ≠ 0 ∧
          (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨emb b, hb⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
      (Rpd.R₂.residue ⟨emb b, hb⟩ ≠ 0 → ∃ k : ℕ, PowerSeries.coeff k (Θ b) ∉ maximalIdeal ↥A) := by
  classical

  have hιP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1 = (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) := by
    show (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1) = _
    rw [hP0]
  rw [← hιP0]
  intro hsp hx Θ hC hfil hsurj b hb
  haveI hCint : IsIntegral (𝔛.Mfib A hA ρ hρ).C := (𝔛.Mfib A hA ρ hρ).isIntegral
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 1
  haveI : IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := 𝔛.fibre_reduced A hA ρ hρ

  let σ : ↥A →+* (XO (ΓM M H) hj ρ).presheaf.stalk ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) :=
    ((XO (ΓM M H) hj ρ).presheaf.germ ⊤ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) trivial).hom.comp
      ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
  letI : Algebra ↥A ((XO (ΓM M H) hj ρ).presheaf.stalk ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1)) := σ.toAlgebra

  have hE := RingHom.forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff Θ _ (fun a => hC a) hfil hsurj
    (IsLocalRing.maximalIdeal ↥A)

  have hut : (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])) ≫ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) = 𝟙 _ := pullback.lift_snd _ _ _
  have hχσ : ∀ a : ↥A, (Scheme.stalkClosedPointTo (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp]))).hom (((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom
      (((XO (ΓM M H) hj ρ).presheaf.germ ⊤ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) trivial).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)))) = a := by
    intro a
    rw [← CommRingCat.comp_apply ((XO (ΓM M H) hj ρ).presheaf.germ ⊤ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) trivial), TopCat.Presheaf.germ_stalkSpecializes,
      Scheme.stalkClosedPointTo, CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap_apply]
    have h3 : (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop ≫ Scheme.Hom.appTop (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])) = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hut, Scheme.Hom.id_appTop]
    have h2 : (Scheme.Hom.appTop (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp]))).hom ((pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a)) =
        (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom a := by
      rw [← CommRingCat.comp_apply, h3]
      rfl
    erw [h2]
    erw [← CommRingCat.comp_apply, AlgebraicGeometry.germ_stalkClosedPointIso_hom]
    exact Iso.inv_hom_id_apply _ _
  have hχσ' : ∀ a : ↥A, ((Scheme.stalkClosedPointTo (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp]))).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom) (σ a) = a := fun a => by
    simp only [σ, RingHom.coe_comp, Function.comp_apply]
    exact hχσ a

  have Hbig : IsPullback ((bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ≫ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρ)) := by
    rw [bcMap_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact IsPullback.of_hasPullback _ _
  have Hsq : IsPullback (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :=
    Hbig.of_right (bcMap_snd (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) (IsPullback.of_hasPullback _ _)
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI hbcCI : IsClosedImmersion (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) := MorphismProperty.of_isPullback Hsq.flip inferInstance
  haveI : IsClosedImmersion (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) := inferInstance
  have hlamsurj : Function.Surjective (Scheme.Hom.stalkMap (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) P0.1).hom := Scheme.Hom.stalkMap_surjective _ _

  have hιsnd : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) ≫ (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) = (𝔛.Mfib A hA ρ hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
    rw [Category.assoc, Category.assoc, bcMap_snd, ← Category.assoc (𝔛.comp A hA ρ hρ 1), 𝔛.comp_over A hA ρ hρ 1,
      ← Category.assoc, 𝔛.hefib A hA ρ hρ]
  have hJker : (IsLocalRing.maximalIdeal ↥A).map σ ≤ RingHom.ker (Scheme.Hom.stalkMap (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) P0.1).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [σ, RingHom.coe_comp, Function.comp_apply]
    rw [Scheme.Hom.germ_stalkMap_apply]
    rw [ResidueOrdAux.app_top_apply_of_comp_eq _ _ _ _ hιsnd]
    rw [ResidueOrdAux.specMap_appTop_ΓSpecIso_inv_apply, CommRingCat.hom_ofHom,
      (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero, map_zero]
    exact map_zero _

  have hy : (𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base P0.1) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by
    have : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 ∉ Set.range (𝔛.comp A hA ρ hρ 0).base := by rw [hP0]; exact hsmooth
    exact this
  haveI hG2 : IsIso ((𝔛.comp A hA ρ hρ 1).stalkMap ((𝔛.efib A hA ρ hρ).base P0.1)) :=
    AlgebraicGeometry.isIso_stalkMap_of_isClosedImmersion_of_not_mem_range _ _
      (fun z => (𝔛.comp_jointly_surjective A hA ρ hρ z).symm) _ hy
  haveI hGe : IsIso ((𝔛.efib A hA ρ hρ).stalkMap P0.1) := inferInstance
  have hG1 := ResidueOrdAux.ker_stalkMap_le_map_of_isPullback (IsLocalRing.maximalIdeal ↥A) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) Hsq
    ((𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base P0.1))
  have hkerJ : RingHom.ker (Scheme.Hom.stalkMap (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) P0.1).hom ≤ (IsLocalRing.maximalIdeal ↥A).map σ := by
    intro s hs
    rw [RingHom.mem_ker, ResidueOrdAux.stalkMap_comp₃_apply] at hs
    have hs' := ResidueOrdAux.eq_zero_of_isIso_apply _ _ (ResidueOrdAux.eq_zero_of_isIso_apply _ _ hs)
    exact hG1 hs'

  have hmainres := ResidueOrdAux.main_reduction_law ((Scheme.stalkClosedPointTo (pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp]))).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom) σ hχσ' Θ hE (Scheme.Hom.stalkMap (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) P0.1).hom hlamsurj hJker hkerJ
    (fun d => (𝔛.Mfib A hA ρ hρ).ffEquiv.symm (algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P0.1) (𝔛.Mfib A hA ρ hρ).C.functionField d)) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord
    (fun k d h1 h2 => hP0Q ▸ ResidueOrdAux.CurveModel.read_ne_zero_and_ord_eq (𝔛.Mfib A hA ρ hρ) P0 k d h1 h2)
    (fun d hd => ResidueOrdAux.CurveModel.exists_not_mem_pow_of_read_ne_zero (𝔛.Mfib A hA ρ hρ) P0 d hd) b

  obtain ⟨V, hxV, g, hbg⟩ := (XO (ΓM M H) hj ρ).presheaf.exists_germ_eq b
  have hgenV : (genericPoint (𝔛.Meta).C) ∈ 𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ V) := hsp.mem_open V.2 hxV
  have hi : 𝔛.ξzero A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V :=
    ((genericPoint_specializes P0.1).map (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).continuous).mem_open V.2 hxV
  obtain ⟨h₁, ⟨hg₀, hres⟩, -⟩ :=
    (ModularCurve.XHDRModelAtP.readA_mem_integers_and_residue_eq_restrict_comp_of_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
      θ Psp Rpd hwgen V hgenV g).2 hi
  subst hbg

  have ha := ResidueOrdAux.stalkMap_stalkMap_stalkSpecializes_germ 𝔛.eeta (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) (genericPoint (𝔛.Meta).C) hsp V hxV g
  have hemb : ((𝔛.Meta).ffEquiv.symm.toRingHom.comp ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp ((Scheme.Hom.stalkMap (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))) (((XO (ΓM M H) hj ρ).presheaf.germ V ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) hxV).hom g) = ((𝔛.Meta).ffEquiv.symm.toRingHom.comp (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ V)).hom.comp (Scheme.Hom.app (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) V).hom))) g := congrArg (𝔛.Meta).ffEquiv.symm ha
  have hb2 : Rpd.R₂.residue ⟨((𝔛.Meta).ffEquiv.symm.toRingHom.comp ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp ((Scheme.Hom.stalkMap (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))) (((XO (ΓM M H) hj ρ).presheaf.germ V ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) hxV).hom g), hb⟩ = Rpd.R₂.residue ⟨((𝔛.Meta).ffEquiv.symm.toRingHom.comp (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp ((𝔛.eeta.app ((pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) ⁻¹ᵁ V)).hom.comp (Scheme.Hom.app (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) V).hom))) g, h₁⟩ :=
    congrArg Rpd.R₂.residue (Subtype.ext hemb)

  have hd := ResidueOrdAux.stalkSpecializes_stalkMap_germ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) P0.1 (genericPoint (𝔛.Mfib A hA ρ hρ).C)
    (genericPoint_specializes P0.1) V hxV g
  have hdock : Rpd.R₂.residue ⟨((𝔛.Meta).ffEquiv.symm.toRingHom.comp ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp ((Scheme.Hom.stalkMap (pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])) (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))) (((XO (ΓM M H) hj ρ).presheaf.germ V ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) hxV).hom g), hb⟩ =
      (𝔛.Mfib A hA ρ hρ).ffEquiv.symm (algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P0.1) (𝔛.Mfib A hA ρ hρ).C.functionField ((Scheme.Hom.stalkMap (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl) P0.1).hom (((XO (ΓM M H) hj ρ).presheaf.germ V ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base P0.1) hxV).hom g))) := by
    exact hb2.trans (hres.trans (congrArg (𝔛.Mfib A hA ρ hρ).ffEquiv.symm hd.symm))
  rw [hdock]
  exact hmainres

end S_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd (solution)
