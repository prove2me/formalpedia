-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a38d60bc-6231-5db6-8f1c-0d3383229615

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_XHDRLevel_qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin
import Theorems.Thm_ModularCurve_XHDRModelAtP_residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul"
p2m_attr_erase "simp" "KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

noncomputable section

namespace ResRestrictCore

open scoped nonZeroDivisors

theorem ringHom_eq_of_ker_eq_of_eqOn_of_closure_image_eq_top
    {R F : Type*} [CommRing R] [Field F] (φ₁ φ₂ : R →+* F)
    (hker : RingHom.ker φ₁ = RingHom.ker φ₂)
    (S : Set R) (hS : ∀ s ∈ S, φ₁ s = φ₂ s)
    (hgen : Subfield.closure (φ₂ '' S) = ⊤) :
    φ₁ = φ₂ := by
  classical

  set P : Ideal R := RingHom.ker φ₂ with hP
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime φ₂

  let ψ₁ : R ⧸ P →+* F := Ideal.Quotient.lift P φ₁ (fun a ha => by
    have : a ∈ RingHom.ker φ₁ := by rw [hker]; exact ha
    exact this)
  let ψ₂ : R ⧸ P →+* F := Ideal.Quotient.lift P φ₂ (fun a ha => ha)
  have hψ₁ : ∀ r, ψ₁ (Ideal.Quotient.mk P r) = φ₁ r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hψ₂ : ∀ r, ψ₂ (Ideal.Quotient.mk P r) = φ₂ r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hinj₁ : Function.Injective ψ₁ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hψ₁] at hx
    have : r ∈ RingHom.ker φ₁ := hx
    rw [hker] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have hinj₂ : Function.Injective ψ₂ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hψ₂] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  let E := FractionRing (R ⧸ P)
  let χ₁ : E →+* F := IsFractionRing.lift (K := E) hinj₁
  let χ₂ : E →+* F := IsFractionRing.lift (K := E) hinj₂
  have hχ₁ : ∀ x : R ⧸ P, χ₁ (algebraMap (R ⧸ P) E x) = ψ₁ x := fun x => IsFractionRing.lift_algebraMap hinj₁ x
  have hχ₂ : ∀ x : R ⧸ P, χ₂ (algebraMap (R ⧸ P) E x) = ψ₂ x := fun x => IsFractionRing.lift_algebraMap hinj₂ x

  have hsurj : Function.Surjective χ₂ := by
    rw [← RingHom.fieldRange_eq_top_iff, eq_top_iff, ← hgen]
    refine Subfield.closure_le.mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨algebraMap (R ⧸ P) E (Ideal.Quotient.mk P s), by rw [hχ₂, hψ₂]⟩
  have hbij : Function.Bijective χ₂ := ⟨χ₂.injective, hsurj⟩
  let e₂ : E ≃+* F := RingEquiv.ofBijective χ₂ hbij
  have he₂ : ∀ x, e₂ x = χ₂ x := fun _ => rfl

  let τ : F →+* F := χ₁.comp e₂.symm.toRingHom
  have hτS : ∀ s ∈ S, τ (φ₂ s) = φ₂ s := by
    intro s hs
    have h1 : e₂.symm (φ₂ s) = algebraMap (R ⧸ P) E (Ideal.Quotient.mk P s) := by
      apply e₂.injective
      rw [RingEquiv.apply_symm_apply, he₂, hχ₂, hψ₂]
    show χ₁ (e₂.symm (φ₂ s)) = φ₂ s
    rw [h1, hχ₁, hψ₁, hS s hs]

  let Fix : Subfield F :=
    { carrier := {x | τ x = x}
      mul_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_mul, ha, hb]
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [map_add, ha, hb]
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simp only [Set.mem_setOf_eq] at ha ⊢; rw [map_neg, ha]
      inv_mem' := fun a ha => by simp only [Set.mem_setOf_eq] at ha ⊢; rw [map_inv₀, ha] }
  have hFix : (⊤ : Subfield F) ≤ Fix := by
    rw [← hgen]
    refine Subfield.closure_le.mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hτS s hs
  have hτ : ∀ x, τ x = x := fun x => hFix (Subfield.mem_top x)

  ext r
  have h1 : φ₁ r = χ₁ (algebraMap (R ⧸ P) E (Ideal.Quotient.mk P r)) := by rw [hχ₁, hψ₁]
  have h2 : φ₂ r = χ₂ (algebraMap (R ⧸ P) E (Ideal.Quotient.mk P r)) := by rw [hχ₂, hψ₂]
  rw [h1, h2]
  set x := algebraMap (R ⧸ P) E (Ideal.Quotient.mk P r)
  have : τ (χ₂ x) = χ₂ x := hτ _
  have h3 : e₂.symm (χ₂ x) = x := by
    apply e₂.injective; rw [RingEquiv.apply_symm_apply, he₂]
  calc χ₁ x = χ₁ (e₂.symm (χ₂ x)) := by rw [h3]
    _ = τ (χ₂ x) := rfl
    _ = χ₂ x := this

end ResRestrictCore

namespace ResRestrictAux
open AlgebraicGeometry CategoryTheory

theorem stalkMap_germ_top {X Y : Scheme} (f : X ⟶ Y) (x : X) (y : Γ(Y, ⊤)) :
    f.stalkMap x (Y.presheaf.germ ⊤ (f.base x) trivial y) = X.presheaf.germ ⊤ x trivial (f.appTop y) :=
  Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial y

theorem comp_appTop_apply {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (t : Γ(Z, ⊤)) :
    (f ≫ g).appTop t = f.appTop (g.appTop t) := rfl

theorem ΓSpecIso_inv_appTop {R S : CommRingCat} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop).hom r = (φ ≫ (Scheme.ΓSpecIso S).inv).hom r
  rw [Scheme.ΓSpecIso_inv_naturality]

end ResRestrictAux

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    (∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)) (hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V),
      letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
        (𝔛.Meta).ffEquiv.symm.toRingHom.comp
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
            ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
      ∃ h : readA g ∈ Rpd.R₁.integers,
        (IsUnit ((XO (ΓM M H) hj ρ).presheaf.germ V _ hi g) ↔ Rpd.R₁.residue ⟨readA g, h⟩ ≠ 0)) →
    ∀ (V : (XO (ΓM M H) hj ρ).Opens) (hgenV : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V))
      (g : Γ(XO (ΓM M H) hj ρ, V)) (hi : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ V),
    letI readA : Γ(XO (ΓM M H) hj ρ, V) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ V)) (genericPoint (𝔛.Meta).C) hgenV).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ V)).hom.comp (prA.app V).hom))
    ∀ h : readA g ∈ Rpd.R₁.integers,
    letI := (𝔛.Mfib A hA ρ hρ).isIntegral
    ∃ hg₀ : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V,
      Rpd.R₁.residue ⟨readA g, h⟩ =
        (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
          (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ V) (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg₀)
            (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app V).hom g)) := by
  intro HDOM V hgenV g hi h
  refine ⟨hi, ?_⟩

  let XA : Scheme.{0} := XO (ΓM M H) hj ρ
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prA : XQ ⟶ XA :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
  let bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
  letI := (𝔛.Mfib A hA ρ hρ).isIntegral
  let η := genericPoint (𝔛.Mfib A hA ρ hρ).C
  let f : (𝔛.Mfib A hA ρ hρ).C ⟶ XA := 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA
  have hfη : f.base η = 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl := rfl

  let Vfin : XA.Opens := (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)
  have hy1 : coeffMap A.subtype (1 : LaurentSeries ↥A) =
      coeffEmb (AlgebraicClosure ℚ) ((((1 : ↥(chartAlgFin p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) := by
    simp only [coeffMap, coeffEmb]
    ext n
    simp
  obtain ⟨hiFin, hgenFin, -, -⟩ := ModularCurve.XHDRModelAtP.residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd 1 1 hy1
  let W : XA.Opens := V ⊓ Vfin
  have hiW : 𝔛.ξinf A hA ρ hρ ρ (IsLocalRing.residue ↥A) rfl ∈ W := ⟨hi, hiFin⟩
  have hgenW : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ W) := ⟨hgenV, hgenFin⟩
  have hηW : η ∈ f ⁻¹ᵁ W := hiW

  let readW : Γ(XA, W) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ W)) (genericPoint (𝔛.Meta).C) hgenW).hom.comp
        ((𝔛.eeta.app (prA ⁻¹ᵁ W)).hom.comp (prA.app W).hom))
  have hint : ∀ r : Γ(XA, W), readW r ∈ Rpd.R₁.integers := fun r => (HDOM W hgenW r hiW).choose
  have hunit : ∀ r : Γ(XA, W), IsUnit (XA.presheaf.germ W _ hiW r) ↔ Rpd.R₁.residue ⟨readW r, hint r⟩ ≠ 0 :=
    fun r => (HDOM W hgenW r hiW).choose_spec
  let Φ₁ : Γ(XA, W) →+* JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A) := Rpd.R₁.residue.comp (readW.codRestrict Rpd.R₁.integers hint)
  have hΦ₁ : ∀ r, Φ₁ r = Rpd.R₁.residue ⟨readW r, hint r⟩ := fun r => rfl
  let Φ₂ : Γ(XA, W) →+* JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A) :=
    (𝔛.Mfib A hA ρ hρ).ffEquiv.symm.toRingHom.comp
      ((((𝔛.Mfib A hA ρ hρ).C.presheaf.germ (f ⁻¹ᵁ W) η hηW).hom).comp (f.app W).hom)
  have hΦ₂ : ∀ r, Φ₂ r = (𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.presheaf.germ (f ⁻¹ᵁ W) η hηW ((f.app W).hom r)) :=
    fun r => rfl

  have hker : RingHom.ker Φ₁ = RingHom.ker Φ₂ := by
    ext r
    simp only [RingHom.mem_ker, hΦ₁, hΦ₂]
    rw [map_eq_zero_iff _ (𝔛.Mfib A hA ρ hρ).ffEquiv.symm.injective, ← Scheme.Hom.germ_stalkMap_apply f W η hiW r]
    have hloc : IsUnit (f.stalkMap η (XA.presheaf.germ W _ hiW r)) ↔ IsUnit (XA.presheaf.germ W _ hiW r) :=
      isUnit_map_iff (f.stalkMap η).hom _
    rw [← not_iff_not, ← ne_eq, ← hunit r, ← hloc, isUnit_iff_ne_zero]

  let sec : ↥(chartAlgFin p (ΓN p M H hpM) hj) → Γ(XA, W) := fun b =>
    XA.presheaf.map (homOfLE inf_le_right).op
      (((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).app ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
        (((ιFin p (ΓM M H) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv (𝔛.iota0 b))))
  let cst : ↥A → Γ(XA, W) := fun a =>
    XA.presheaf.map (homOfLE le_top).op ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))
  let S : Set Γ(XA, W) :=
    {r | ∃ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) ∧
        r = sec b} ∪
    {r | ∃ a : ↥A, r = cst a}

  have hconst₁ : ∀ a : ↥A, Φ₁ (cst a) = algebraMap (IsLocalRing.ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) (IsLocalRing.residue ↥A a) := by
    intro a
    rw [hΦ₁, ← Rpd.R₁.residue_algebraMap a]
    congr 1
    apply Subtype.ext
    show readW (cst a) = algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)
    apply (𝔛.Meta).ffEquiv.injective
    rw [(𝔛.Meta).ffEquiv_algebraMap]

    have hgb : (𝔛.eeta ≫ prA) ≫ XO.toBase (ΓM M H) hj ρ =
        (𝔛.Meta).toBase ≫ Spec.map (CommRingCat.ofHom A.subtype) := by
      simp only [prA, XO.toBase, Category.assoc, pullback.lift_snd, pullback.map]
      rw [← Category.assoc, 𝔛.heeta]
    have hsec : (𝔛.eeta ≫ prA).appTop ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))
        = (𝔛.Meta).toBase.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (a : AlgebraicClosure ℚ)) := by
      rw [← ResRestrictAux.comp_appTop_apply, hgb, ResRestrictAux.comp_appTop_apply,
        ResRestrictAux.ΓSpecIso_inv_appTop]
      rfl

    have step1 : (𝔛.Meta).ffEquiv (readW (cst a)) =
        (𝔛.Meta).C.presheaf.germ ⊤ (genericPoint (𝔛.Meta).C) trivial
          ((𝔛.eeta ≫ prA).appTop ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) := by
      simp only [readW, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
      rw [← ResRestrictAux.stalkMap_germ_top (𝔛.eeta ≫ prA) (genericPoint (𝔛.Meta).C)]
      rw [← TopCat.Presheaf.germ_res_apply XA.presheaf (homOfLE le_top) _
        (show (𝔛.eeta ≫ prA).base (genericPoint (𝔛.Meta).C) ∈ W from hgenW)
        ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))]
      rw [Scheme.Hom.germ_stalkMap_apply]
      rfl
    rw [step1, hsec]
    rfl
  have hconst₂ : ∀ a : ↥A, Φ₂ (cst a) = algebraMap (IsLocalRing.ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) (IsLocalRing.residue ↥A a) := by
    intro a
    rw [hΦ₂]
    apply (𝔛.Mfib A hA ρ hρ).ffEquiv.injective
    rw [RingEquiv.apply_symm_apply, (𝔛.Mfib A hA ρ hρ).ffEquiv_algebraMap]

    have hfb : f ≫ XO.toBase (ΓM M H) hj ρ =
        (𝔛.Mfib A hA ρ hρ).toBase ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) := by
      simp only [f, bcA, XO.toBase, Category.assoc, bcMap_snd]
      rw [← Category.assoc (𝔛.comp A hA ρ hρ 0), 𝔛.comp_over A hA ρ hρ 0, ← Category.assoc, 𝔛.hefib A hA ρ hρ]

    have hsec : f.appTop ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))
        = (𝔛.Mfib A hA ρ hρ).toBase.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv (IsLocalRing.residue ↥A a)) := by
      rw [← ResRestrictAux.comp_appTop_apply, hfb, ResRestrictAux.comp_appTop_apply,
        ResRestrictAux.ΓSpecIso_inv_appTop]
      rfl

    have step1 : (𝔛.Mfib A hA ρ hρ).C.presheaf.germ (f ⁻¹ᵁ W) η hηW ((f.app W).hom (cst a)) =
        (𝔛.Mfib A hA ρ hρ).C.presheaf.germ ⊤ η trivial
          (f.appTop ((XO.toBase (ΓM M H) hj ρ).appTop ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))) := by
      rw [← Scheme.Hom.germ_stalkMap_apply f W η hiW, ← ResRestrictAux.stalkMap_germ_top f η]
      congr 1
      exact TopCat.Presheaf.germ_res_apply XA.presheaf (homOfLE le_top) _ hiW _
    rw [step1, hsec]
    rfl

  have hB1 : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
      ((Φ₁ (sec b) : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
    intro b y hy
    obtain ⟨hiF, hgenF, ⟨h1, hB1'⟩, -⟩ := ModularCurve.XHDRModelAtP.residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd b y hy
    rw [hΦ₁]
    convert hB1' using 4

    have e1 : ∀ (U : XA.Opens) (hU : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U)) (s : Γ(XA, U)),
        (𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U)) (genericPoint (𝔛.Meta).C) hU
            ((𝔛.eeta.app (prA ⁻¹ᵁ U)).hom ((prA.app U).hom s))
          = (𝔛.eeta ≫ prA).stalkMap (genericPoint (𝔛.Meta).C)
              (XA.presheaf.germ U ((𝔛.eeta ≫ prA).base (genericPoint (𝔛.Meta).C)) hU s) := by
      intro U hU s
      rw [Scheme.Hom.germ_stalkMap_apply]
      first
        | rfl
        | simp only [Scheme.comp_app, CommRingCat.comp_apply]; rfl
    simp only [readW, RingHom.coe_comp, Function.comp_apply]
    congr 1
    rw [e1 W hgenW, e1 Vfin hgenF]
    congr 1
    exact TopCat.Presheaf.germ_res_apply XA.presheaf (homOfLE inf_le_right) _ hgenW _
  have hB2 : ∀ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
      coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
      ((Φ₂ (sec b) : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
    intro b y hy
    obtain ⟨hiF, hgenF, -, ⟨hg₀', hB2'⟩⟩ := ModularCurve.XHDRModelAtP.residue_readA_chart_eq_and_restrict_comp_zero_chart_eq_coeffMap_of_coeffMap_eq_coeffEmb p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ Psp Rpd b y hy
    rw [hΦ₂]
    convert hB2' using 4
    rw [← Scheme.Hom.germ_stalkMap_apply f W η hiW, ← Scheme.Hom.germ_stalkMap_apply f Vfin η hiF]
    congr 1
    exact TopCat.Presheaf.germ_res_apply XA.presheaf (homOfLE inf_le_right) _ hiW _

  have hS : ∀ s ∈ S, Φ₁ s = Φ₂ s := by
    rintro s (⟨b, y, hy, rfl⟩ | ⟨a, rfl⟩)
    · exact Subtype.ext ((hB1 b y hy).trans (hB2 b y hy).symm)
    · rw [hconst₁, hconst₂]

  have hgen : Subfield.closure (Φ₂ '' S) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let ιF : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A) →+* LaurentSeries (IsLocalRing.ResidueField ↥A) :=
      (qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)).toSubfield.subtype
    have hιF : Function.Injective ιF := Subtype.val_injective
    suffices hsuff : (qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)).toSubfield ≤ (Subfield.closure (Φ₂ '' S)).map ιF by
      obtain ⟨x', hx', hxx'⟩ := Subfield.mem_map.mp (hsuff x.2)
      have : x' = x := hιF hxx'
      rw [← this]; exact hx'
    rw [RingHom.map_field_closure]
    intro z hz
    have hz' : z ∈ IntermediateField.adjoin (IsLocalRing.ResidueField ↥A)
        {x : LaurentSeries (IsLocalRing.ResidueField ↥A) |
          ∃ (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
            coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) ∧
            x = coeffMap (IsLocalRing.residue ↥A) y} :=
      ModularCurve.XHDRLevel.qExpFunctionFieldC_residueField_le_adjoin_coeffMap_residue_of_mem_chartAlgFin p M H hpM hpM2 hj A hA hz
    have hz'' := (IntermediateField.mem_toSubfield _ _).mpr hz'
    rw [IntermediateField.adjoin_toSubfield] at hz''
    refine (Subfield.closure_le.mpr ?_) hz''
    rintro w (⟨c, rfl⟩ | ⟨b, y, hy, rfl⟩)
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine Subfield.subset_closure ⟨Φ₂ (cst a), ⟨cst a, Or.inr ⟨a, rfl⟩, rfl⟩, ?_⟩
      rw [hconst₂]
      rfl
    · exact Subfield.subset_closure ⟨Φ₂ (sec b), ⟨sec b, Or.inl ⟨b, y, hy, rfl⟩, rfl⟩, hB2 b y hy⟩
  have hΦ : Φ₁ = Φ₂ := ResRestrictCore.ringHom_eq_of_ker_eq_of_eqOn_of_closure_image_eq_top Φ₁ Φ₂ hker S hS hgen

  have hgW := congrArg (fun (F : Γ(XA, W) →+* JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) => F (XA.presheaf.map (homOfLE inf_le_left).op g)) hΦ
  simp only [hΦ₁, hΦ₂] at hgW
  convert hgW using 3
  ·
    have e1 : ∀ (U : XA.Opens) (hU : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U)) (s : Γ(XA, U)),
        (𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U)) (genericPoint (𝔛.Meta).C) hU
            ((𝔛.eeta.app (prA ⁻¹ᵁ U)).hom ((prA.app U).hom s))
          = (𝔛.eeta ≫ prA).stalkMap (genericPoint (𝔛.Meta).C)
              (XA.presheaf.germ U ((𝔛.eeta ≫ prA).base (genericPoint (𝔛.Meta).C)) hU s) := by
      intro U hU s
      rw [Scheme.Hom.germ_stalkMap_apply]
      first
        | rfl
        | simp only [Scheme.comp_app, CommRingCat.comp_apply]; rfl
    simp only [readW, RingHom.coe_comp, Function.comp_apply]
    congr 1
    rw [e1 V hgenV g, e1 W hgenW]
    congr 1
    exact (TopCat.Presheaf.germ_res_apply XA.presheaf (homOfLE inf_le_left) _ hgenW g).symm
  ·
    rw [← Scheme.Hom.germ_stalkMap_apply f V η hi g, ← Scheme.Hom.germ_stalkMap_apply f W η hiW]
    congr 1
    exact (TopCat.Presheaf.germ_res_apply XA.presheaf (homOfLE inf_le_left) _ hiW g).symm

end

end S_ModularCurve_XHDRModelAtP_residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_residue_readA_eq_restrict_comp_zero_of_forall_isUnit_germ_iff_residue_ne_zero (solution)
