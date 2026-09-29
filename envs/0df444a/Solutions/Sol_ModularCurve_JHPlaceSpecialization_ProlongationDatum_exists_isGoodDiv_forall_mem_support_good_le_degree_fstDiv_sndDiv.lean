-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fa3ab9a1-89a9-53c4-b772-eff27f5249c6

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_pos_sp_sub_algebraMap_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

namespace GoodAuxH

theorem ramificationIndexAlong_pos {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem pos_of_natMul_pos {e : ℕ} {x : ℤ} (h : 0 < (e : ℤ) * x) : 0 < x := by
  by_contra hle
  push Not at hle
  have := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg e) hle
  omega

theorem coe_sub_ne_zero_of_coeff {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (x : ↥F) (hx : ((x : ↥F) : LaurentSeries K) = jqModC K) (s : K) :
    x - algebraMap K (↥F) s ≠ 0 := by
  intro h
  have h2 : jqModC K = algebraMap K (LaurentSeries K) s := by
    have h1 : ((x - algebraMap K (↥F) s : ↥F) : LaurentSeries K) = 0 := by rw [h]; rfl
    have h3 : ((x - algebraMap K (↥F) s : ↥F) : LaurentSeries K) = jqModC K - algebraMap K (LaurentSeries K) s := by
      rw [← hx]; rfl
    rw [h3] at h1
    exact sub_eq_zero.mp h1
  exact ModularCurve.transcendental_jqModC K (h2 ▸ isAlgebraic_algebraMap s)

theorem coe_ne_zero_of_coeff {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K))
    (x : ↥F) (hx : ((x : ↥F) : LaurentSeries K) = jqModC K) : x ≠ 0 := by
  have h := coe_sub_ne_zero_of_coeff F x hx 0
  rwa [map_zero, sub_zero] at h

end GoodAuxH

namespace GoodAuxH

section Frame

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
variable [NeZero (M / p)]
variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
variable [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

omit [Fact p.Prime] [NeZero M] [NeZero (M / p)] in

theorem exists_coe_eq_jqModC :
    ∃ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
        jqModC (AlgebraicClosure ℚ) := by
  have hmem : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) :=
    x0_le_xHFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM)
      (intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _))
  refine ⟨⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩, ?_⟩
  show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
  exact coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

omit [Fact p.Prime] [NeZero M] [NeZero (M / p)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem exists_coe_eq_jqModC_bar :
    ∃ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A),
      ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) :=
  ⟨⟨jqModC (ResidueField ↥A), intFormRatiosC_subset (ResidueField ↥A) _
      (ModularCurve.jqModC_mem_intFormRatiosC (ResidueField ↥A) _)⟩, rfl⟩

include hpM2 hA in
theorem goodJ (Psp : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hu : ((u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (S : Finset (ResidueField ↥A)) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hnopole : ¬ (Psp.reduceFst α hα V).ord xb < 0)
    (hnoval : ∀ s ∈ S, ¬ 0 < (Psp.reduceFst α hα V).ord
      (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) s)) :
    ∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧
        IsLocalRing.residue ↥A a ∉ S := by
  intro xj hxj
  have hxju : xj = α u := Subtype.ext (by rw [hxj, hα_coe u, hu])
  have htrans : ∀ a : ↥A,
      α (u - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) =
        xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := fun a => by
    rw [map_sub, AlgHom.commutes, hxju]
  have hordV : ∀ a : ↥A,
      V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) =
        (Place.ramificationIndexAlong α V : ℤ) *
          (V.restrictAlong α hα).ord
            (u - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) := fun a => by
    rw [← htrans, Place.ord_restrictAlong]
  by_cases hex : ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
  · obtain ⟨a, ha⟩ := hex
    refine ⟨a, ha, fun hmem => ?_⟩
    have hw : 0 < (V.restrictAlong α hα).ord
        (u - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) := by
      rw [hordV] at ha
      exact pos_of_natMul_pos ha
    have hd := JHPlaceSpecialization.ord_pos_sp_sub_algebraMap_of_ord_pos p M H hpM hpM2 A hA Psp u xb hu hxb
      (V.restrictAlong α hα) a hw
    exact hnoval _ hmem hd
  · push Not at hex
    exfalso
    apply hnopole
    have hd := JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp u xb hu hxb
      (V.restrictAlong α hα) (fun a => ?_)
    · exact hd
    · by_contra hlt
      push Not at hlt
      have h1 := hex a
      rw [hordV] at h1
      have h2 : 0 < (Place.ramificationIndexAlong α V : ℤ) *
          (V.restrictAlong α hα).ord
            (u - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) :=
        mul_pos (Int.natCast_pos.mpr (ramificationIndexAlong_pos α hα V)) hlt
      omega

omit [NeZero M] [NeZero (M / p)] [IsAlgClosed (ResidueField ↥A)] in
variable {p M H hpM A} in

theorem not_isStrictFst_of_isStrictSnd (Psp : JHPlaceSpecialization p M H hpM A)
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    {V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (h' : Psp.IsStrictSnd α β hα hβ δ V) :
    ¬ Psp.IsStrictFst α β hα hβ δ V := fun h =>
  h.2 (by
    show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V))) =
      Psp.reduceFst α hα V
    rw [h.1]
    exact h'.1.symm)

end Frame

end GoodAuxH

namespace GoodAuxH

theorem exists_badset {κ Fb : Type*} [Field κ] [Field Fb] [Algebra κ Fb] [HasPrincipalDivisors κ Fb]
    (φ δ : Place κ Fb → Place κ Fb) (hφ : Function.Injective φ) (hδ : Function.Injective δ)
    (xb : Fb) (hxb0 : xb ≠ 0) (hxbs : ∀ s : κ, xb - algebraMap κ Fb s ≠ 0)
    (S : Finset κ) (B : Finset (Place κ Fb)) (t₁ t₂ : Place κ Fb) :
    ∃ B' : Finset (Place κ Fb), ∀ r, r ∉ B' →
      (r ∉ B ∧ r ≠ t₁ ∧ ¬ r.ord xb < 0 ∧ ∀ s ∈ S, ¬ 0 < r.ord (xb - algebraMap κ Fb s)) ∧
      r ≠ t₂ ∧ δ (φ r) ∉ B ∧ δ (φ r) ≠ t₂ ∧
      (φ r ∉ B ∧ φ r ≠ t₁ ∧ ¬ (φ r).ord xb < 0 ∧ ∀ s ∈ S, ¬ 0 < (φ r).ord (xb - algebraMap κ Fb s)) := by
  classical
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := κ) xb hxb0
  choose Dz hDz using fun s : κ => HasPrincipalDivisors.exists_divisor (K := κ) (xb - algebraMap κ Fb s) (hxbs s)
  have hδφ : Function.Injective (fun v => δ (φ v)) := hδ.comp hφ
  let X : Finset (Place κ Fb) := B ∪ {t₁} ∪ Dj.support ∪ S.biUnion (fun s => (Dz s).support)
  have hXgood : ∀ r, r ∉ X → r ∉ B ∧ r ≠ t₁ ∧ ¬ r.ord xb < 0 ∧ ∀ s ∈ S, ¬ 0 < r.ord (xb - algebraMap κ Fb s) := by
    intro r hr
    simp only [X, Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finsupp.mem_support_iff, not_or,
      not_exists, not_and, not_not] at hr
    obtain ⟨⟨⟨hrB, hrt⟩, hrj⟩, hrz⟩ := hr
    refine ⟨hrB, hrt, ?_, fun s hs => ?_⟩
    · rw [← hDj r, hrj]; exact lt_irrefl 0
    · rw [← (hDz s).1 r, hrz s hs]; exact lt_irrefl 0
  refine ⟨X ∪ {t₂} ∪ (B ∪ {t₂}).preimage (fun v => δ (φ v)) hδφ.injOn ∪ X.preimage φ hφ.injOn, fun r hr => ?_⟩
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_preimage, not_or] at hr
  obtain ⟨⟨⟨hrX, hrt₂⟩, hrδB, hrδt⟩, hrφ⟩ := hr
  exact ⟨hXgood r hrX, hrt₂, hrδB, hrδt, hXgood _ hrφ⟩

theorem assemble
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    [IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))]
    (Psp : JHPlaceSpecialization p M H hpM A)
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (S : Finset (ResidueField ↥A)) (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (t₁ t₂ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (n : ℤ)
    (V₁ V₂ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hs₁ : Psp.IsStrictFst α β hα hβ δ V₁) (hs₂ : Psp.IsStrictSnd α β hα hβ δ V₂)
    (hj₁ : ∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V₁.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S)
    (hj₂ : ∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V₂.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S)
    (h₁ : Psp.reduceFst α hα V₁ ∉ B ∧ Psp.reduceSnd β hβ δ V₁ ∉ B ∧ Psp.reduceFst α hα V₁ ≠ t₁ ∧ Psp.reduceSnd β hβ δ V₁ ≠ t₂)
    (h₂ : Psp.reduceFst α hα V₂ ∉ B ∧ Psp.reduceSnd β hβ δ V₂ ∉ B ∧ Psp.reduceFst α hα V₂ ≠ t₁ ∧ Psp.reduceSnd β hβ δ V₂ ≠ t₂) :
    ∃ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, 0 ≤ E V) ∧ Psp.IsGoodDiv α β hα hβ δ E ∧
      (∀ V ∈ E.support,
        (∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
        Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B ∧ Psp.reduceFst α hα V ≠ t₁ ∧ Psp.reduceSnd β hβ δ V ≠ t₂) ∧
      n ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ E)) ∧
      n ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ E)) := by
  have hne : ¬ Psp.IsStrictFst α β hα hβ δ V₂ := not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ hs₂
  have hne' : ¬ Psp.IsStrictSnd α β hα hβ δ V₁ := fun h => not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ h hs₁
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = n.toNat := ⟨_, rfl⟩
  refine ⟨Finsupp.single V₁ (m : ℤ) + Finsupp.single V₂ (m : ℤ), fun W => ?_, fun W hW => ?_, fun W hW => ?_, ?_, ?_⟩
  · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    refine add_nonneg ?_ ?_ <;> split_ifs <;> first | exact Int.natCast_nonneg m | exact le_rfl
  · rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact Or.inl hs₁
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact Or.inr hs₂
  · rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
      exact ⟨hj₁, h₁⟩
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
      exact ⟨hj₂, h₂⟩
  · have hdeg : (Psp.reduceFst α hα V₁).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
    have hE : Psp.fstDiv α β hα hβ δ (Finsupp.single V₁ (m : ℤ) + Finsupp.single V₂ (m : ℤ)) = Finsupp.single V₁ (m : ℤ) := by
      unfold JHPlaceSpecialization.fstDiv
      rw [Finsupp.filter_add, Finsupp.filter_single_of_pos _ hs₁, Finsupp.filter_single_of_neg _ hne, add_zero]
    rw [hE, Finsupp.mapDomain_single, Divisor.degree_single, hdeg]
    simp only [Nat.cast_one, mul_one]
    rw [hm]; exact Int.self_le_toNat n
  · have hdeg : (Psp.reduceSnd β hβ δ V₂).deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed _
    have hE : Psp.sndDiv α β hα hβ δ (Finsupp.single V₁ (m : ℤ) + Finsupp.single V₂ (m : ℤ)) = Finsupp.single V₂ (m : ℤ) := by
      unfold JHPlaceSpecialization.sndDiv
      rw [Finsupp.filter_add, Finsupp.filter_single_of_neg _ hne', Finsupp.filter_single_of_pos _ hs₂, zero_add]
    rw [hE, Finsupp.mapDomain_single, Divisor.degree_single, hdeg]
    simp only [Nat.cast_one, mul_one]
    rw [hm]; exact Int.self_le_toNat n

end GoodAuxH

open GoodAuxH in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))
    (S : Finset (ResidueField ↥A)) (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (t₁ t₂ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (n : ℤ) :
    ∃ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, 0 ≤ E V) ∧ Psp.IsGoodDiv α β hα hβ δ E ∧
      (∀ V ∈ E.support,
        (∀ (xj : ↥(xHFunctionFieldBar M H)), ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
          ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S) ∧
        Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B ∧ Psp.reduceFst α hα V ≠ t₁ ∧ Psp.reduceSnd β hβ δ V ≠ t₂) ∧
      n ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ E)) ∧
      n ≤ Divisor.degree (Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ E)) := by
  clear hcusp hFix

  haveI : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex := inferInstance
  haveI hCO : IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)
      (ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM))
  haveI : HasPrincipalDivisors (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := hCO.toHasPrincipalDivisors

  obtain ⟨u, hu⟩ := exists_coe_eq_jqModC p M H hpM
  obtain ⟨xb, hxb⟩ := exists_coe_eq_jqModC_bar p M H hpM A

  have hφinj : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
  have hδeq := funext hδ
  have hδinj : Function.Injective δ := by
    rw [hδeq]
    exact MulAction.injective _

  obtain ⟨B', hB'⟩ := exists_badset (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) δ hφinj hδinj
    xb (coe_ne_zero_of_coeff _ xb hxb) (fun s => coe_sub_ne_zero_of_coeff _ xb hxb s) S B t₁ t₂

  have hfam := ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
    p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit B' 1 1
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, -, -, hB₁, hB₂, -, -⟩ := hfam
  have hs₁ := hQ₁ 0
  have hs₂ := hQ₂ 0
  obtain ⟨⟨h₁B, h₁t₁, h₁pole, h₁val⟩, -, h₁δB, h₁δt, -⟩ := hB' _ (hB₁ 0)
  obtain ⟨-, h₂t₂, -, -, h₂B, h₂t₁, h₂pole, h₂val⟩ := hB' _ (hB₂ 0)
  obtain ⟨⟨h₂B', -, -, -⟩, -, -, -, -⟩ := hB' _ (hB₂ 0)

  have hsnd₁ : Psp.reduceSnd β hβ δ (Q₁ 0) =
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα (Q₁ 0))) := hs₁.1.symm
  have hfst₂ : Psp.reduceFst α hα (Q₂ 0) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ (Q₂ 0)) := hs₂.1
  rw [← hsnd₁] at h₁δB h₁δt
  rw [← hfst₂] at h₂B h₂t₁ h₂pole h₂val
  exact assemble Psp α β hα hβ δ S B t₁ t₂ n (Q₁ 0) (Q₂ 0) hs₁ hs₂
    (goodJ p M H hpM hpM2 A hA Psp α hα hα_coe u hu xb hxb S (Q₁ 0) h₁pole h₁val)
    (goodJ p M H hpM hpM2 A hA Psp α hα hα_coe u hu xb hxb S (Q₂ 0) h₂pole h₂val)
    ⟨h₁B, h₁δB, h₁t₁, h₁δt⟩ ⟨h₂B, h₂B', h₂t₁, h₂t₂⟩

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_isGoodDiv_forall_mem_support_good_le_degree_fstDiv_sndDiv (solution)
