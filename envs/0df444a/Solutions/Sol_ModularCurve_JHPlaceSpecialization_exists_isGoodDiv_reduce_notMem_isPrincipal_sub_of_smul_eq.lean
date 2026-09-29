-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3eb7912d-5060-589a-8f63-ed8e56e74955

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_pos_sp_sub_algebraMap_of_ord_pos
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace RREngineH

theorem ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at h
  exact lt_irrefl 0 h

theorem sep_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (x : F) {c₁ c₂ : K}
    (h₁ : 0 < v.ord (x - algebraMap K F c₁)) (h₂ : 0 < v.ord (x - algebraMap K F c₂)) : c₁ = c₂ := by
  by_contra hne
  have hsub : (x - algebraMap K F c₂) - (x - algebraMap K F c₁) = algebraMap K F (c₁ - c₂) := by
    rw [map_sub]; ring
  have hv₁ : v.adicValuation (x - algebraMap K F c₁) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₁), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hv₂ : v.adicValuation (x - algebraMap K F c₂) < 1 := by
    rw [v.adicValuation_eq_exp_neg_ord (ne_zero_of_ord_pos v h₂), ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hval : v.adicValuation (algebraMap K F (c₁ - c₂)) < 1 := by
    rw [← hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv₂ hv₁)
  have hord0 : v.ord (algebraMap K F (c₁ - c₂)) = 0 := ConstantReduction.ord_algebraMap v (sub_ne_zero.mpr hne)
  rw [v.adicValuation_eq_exp_neg_ord ((map_ne_zero _).mpr (sub_ne_zero.mpr hne)), hord0] at hval
  simp at hval

open Classical in

noncomputable def jval {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (t : Place K F) : K :=
  if h : ∃ c, 0 < t.ord (x - algebraMap K F c) then h.choose else 0

theorem jval_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (t : Place K F) {c : K}
    (h : 0 < t.ord (x - algebraMap K F c)) : jval x t = c := by
  classical
  have hex : ∃ c', 0 < t.ord (x - algebraMap K F c') := ⟨c, h⟩
  unfold jval
  rw [dif_pos hex]
  exact sep_ord_pos t x hex.choose_spec h

theorem negOrd_sub_algebraMap_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (W : Place K F) (g : F) (c : K) :
    max (-(W.ord (g - algebraMap K F c))) 0 = max (-(W.ord g)) 0 := by
  by_cases hg : W.ord g < 0
  · have hg0 : g ≠ 0 := by rintro rfl; simp at hg
    have hgc0 : g - algebraMap K F c ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h] at hg
      rcases eq_or_ne c 0 with rfl | hc
      · simp at hg
      · rw [ConstantReduction.ord_algebraMap W hc] at hg
        exact lt_irrefl _ hg
    have hv : W.adicValuation (-(algebraMap K F c)) < W.adicValuation g := by
      rw [Valuation.map_neg, W.adicValuation_eq_exp_neg_ord hg0]
      refine lt_of_le_of_lt (W.adicValuation_algebraMap_le_one c) ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    have h1 := Valuation.map_add_eq_of_lt_left _ hv
    rw [← sub_eq_add_neg, W.adicValuation_eq_exp_neg_ord hgc0, W.adicValuation_eq_exp_neg_ord hg0] at h1
    have h2 : W.ord (g - algebraMap K F c) = W.ord g := by
      have := WithZero.exp_injective h1
      omega
    rw [h2]
  · push_neg at hg
    have h1 : 0 ≤ W.ord (g - algebraMap K F c) := by
      rcases eq_or_ne g 0 with rfl | hg0
      · rw [zero_sub, ← map_neg]
        rcases eq_or_ne c 0 with rfl | hc
        · simp
        · rw [ConstantReduction.ord_algebraMap W (neg_ne_zero.mpr hc)]
      · exact W.ord_nonneg_of_mem (sub_mem (W.mem_of_ord_nonneg hg0 hg) (W.algebraMap_mem' c))
    rw [max_eq_right (by omega), max_eq_right (by omega)]

theorem ord_smul_sub_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (v : Place K F) (x : F) (c : K) (h : 0 < v.ord (x - algebraMap K F c)) :
    0 < (g • v).ord (g • x - algebraMap K F (SemilinearAut.baseAut g c)) := by
  have : g • x - algebraMap K F (SemilinearAut.baseAut g c) = g • (x - algebraMap K F c) := by
    rw [SemilinearAut.smul_def, SemilinearAut.smul_def, map_sub, ← SemilinearAut.smul_def,
      ← SemilinearAut.smul_def, SemilinearAut.smul_algebraMap]
  rw [this, SemilinearAut.ord_smul]
  exact h

scoped instance finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

theorem isCurveOver_up (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
  obtain ⟨x, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd

theorem jqModC_mem_Fbar (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) : jqModC K ∈ qExpFunctionFieldC K Γ :=
  intFormRatiosC_subset K Γ (jqModC_mem_intFormRatiosC K Γ)

theorem jqModC_mem_bar (M : ℕ) (H : Subgroup (ZMod M)ˣ) : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar M H := by
  have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (F₀ := xHFunctionField M H)
    (jqModC_mem_Fbar ℚ (CohCarrier.GammaH M H))
  rwa [show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) from
    coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))] at h

end RREngineH
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq.RREngineH"

open RREngineH in

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
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ∀ T : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))),
      ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ V, 0 ≤ E₀ V) ∧ Psp.IsGoodDiv α β hα hβ δ E₀ ∧
          (∀ V ∈ E₀.support, Psp.reduceFst α hα V ∉ T ∧ Psp.reduceSnd β hβ δ V ∉ T) ∧
            0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
              (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • C₀ = C₀) ∧
                0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀) := by
  intro T
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := isCurveOver_up M H
  have hup : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hc] at this
    rw [← this]; ring

  obtain ⟨xb, hxb_def⟩ : ∃ xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), xb =
    ⟨jqModC (ResidueField ↥A), jqModC_mem_Fbar (ResidueField ↥A) _⟩ := ⟨_, rfl⟩
  obtain ⟨xM, hxM_def⟩ : ∃ xM : ↥(xHFunctionFieldBar M H), xM =
    ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_bar M H⟩ := ⟨_, rfl⟩
  obtain ⟨xMp, hxMp_def⟩ : ∃ xMp : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), xMp =
    ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_bar (M / p) (infSubgroup p M H hpM)⟩ := ⟨_, rfl⟩
  have hαx : α xMp = xM := by
    rw [hxMp_def, hxM_def]; exact Subtype.ext (by rw [hα_coe])

  obtain ⟨φ, hφ_def⟩ : ∃ φ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), φ =
    qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := ⟨_, rfl⟩
  obtain ⟨τ, hτ_def⟩ : ∃ τ : SemilinearAut (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), τ =
    SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) := ⟨_, rfl⟩
  have hδτ : ∀ v, δ v = τ • v := fun v => by rw [hτ_def]; exact hδ v

  obtain ⟨kk, ff, gg, pf, pg, -, -, -, hjdiv⟩ := jqModC_mem_intFormRatiosC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)
  have hσxb : qExpArithFrobC p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) • xb = xb :=
    qExpArithFrobC_smul_eq_self_of_coe_eq_intSeriesC_div _ _ _ xb pf pg (by rw [hxb_def]; exact hjdiv)
  have n2 : ∀ (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (d : (ResidueField ↥A)),
      0 < v.ord (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) d) → 0 < (φ v).ord (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (d ^ p)) := by
    intro v d h
    have h1 := ord_smul_sub_pos (qExpArithFrobC p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)) v xb d h
    rw [hσxb, baseAut_qExpArithFrobC_apply] at h1
    rw [hφ_def, qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul]
    exact h1

  have hcomm : ∀ v, φ (τ • v) = τ • φ v := fun v => by
    rw [hφ_def, hτ_def]
    exact qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb) v
  have hFixUp : ∀ r₂ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.Fixed p M H hpM A δ r₂ → JHPlaceSpecialization.Fixed p M H hpM A δ (φ r₂) := by
    intro r₂ h
    unfold JHPlaceSpecialization.Fixed at h ⊢
    rw [← hφ_def] at h ⊢
    rw [hδτ] at h ⊢
    rw [← hcomm, h]

  obtain ⟨Tall, hTall⟩ : ∃ Tall : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), Tall =
    T ∪ T.image φ ∪ T.image (fun v => τ⁻¹ • v) := ⟨_, rfl⟩
  obtain ⟨badT, hbadT⟩ : ∃ badT : Finset (ResidueField ↥A), badT =
    Tall.image (jval xb) := ⟨_, rfl⟩
  obtain ⟨badF, hbadF⟩ : ∃ badF : Finset (ResidueField ↥A), badF =
    hFix.toFinset.image (jval xb) := ⟨_, rfl⟩
  obtain ⟨bad, hbad⟩ : ∃ bad : Finset (ResidueField ↥A), bad =
    (badT ∪ badT.preimage (frobenius (ResidueField ↥A) p) (frobenius_inj (ResidueField ↥A) p).injOn) ∪ badF := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset bad
  rw [hbad] at hc
  simp only [Finset.mem_union, not_or] at hc
  obtain ⟨⟨hc_badT, hc_pre⟩, hc_badF⟩ := hc
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := ↥A) c
  obtain ⟨f, hf_def⟩ : ∃ f : ↥(xHFunctionFieldBar M H), f =
    xM - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ) := ⟨_, rfl⟩

  obtain ⟨Winf, hWinf⟩ : ∃ Winf : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Winf =
    qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) ⟨xM, by rw [hxM_def]; exact order_jqModC_def (AlgebraicClosure ℚ)⟩ := ⟨_, rfl⟩
  have hjpole : xM ∉ Winf.toValuationSubring := by
    rw [hWinf, qInftyPlaceBar_toValuationSubring, mem_qIntegersBar_iff, not_le, hxM_def]
    show (jqModC (AlgebraicClosure ℚ)).order < 0
    rw [order_jqModC_def]; norm_num
  have hfpole : f ∉ Winf.toValuationSubring := by
    intro h
    apply hjpole
    have h' := add_mem h (Winf.algebraMap_mem' (a : AlgebraicClosure ℚ))
    rwa [hf_def, sub_add_cancel] at h'
  have hf0 : f ≠ 0 := fun h => hfpole (h ▸ zero_mem _)
  have hford : Winf.ord f < 0 := by
    by_contra hge
    push_neg at hge
    exact hfpole (Winf.mem_of_ord_nonneg hf0 hge)
  obtain ⟨Df, hDf, hDfdeg⟩ := (IsCurveOver.hasPrincipalDivisors (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))).exists_divisor f hf0
  obtain ⟨E₀, hE₀def⟩ : ∃ E₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), E₀ =
    Df.mapRange (fun n => max n 0) (by simp) := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), C₀ =
    Df.mapRange (fun n => max (-n) 0) (by simp) := ⟨_, rfl⟩
  have hE₀ : ∀ V, E₀ V = max (V.ord f) 0 := fun V => by simp only [hE₀def, Finsupp.mapRange_apply, hDf V]
  have hC₀ : ∀ V, C₀ V = max (-(V.ord f)) 0 := fun V => by simp only [hC₀def, Finsupp.mapRange_apply, hDf V]

  have hpin : ∀ V ∈ E₀.support, 0 < (Psp.reduceFst α hα V).ord (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c) := by
    intro V hV
    have hpos : 0 < V.ord f := by
      have h := Finsupp.mem_support_iff.mp hV
      rw [hE₀] at h
      by_contra hle
      push_neg at hle
      exact h (max_eq_right (by omega))
    have htrans : α (xMp - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) = f := by
      rw [map_sub, hαx, AlgHom.commutes, hf_def]
    have hord := Place.ord_restrictAlong α hα V (xMp - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ))
    rw [htrans] at hord
    have hre : 0 < (V.restrictAlong α hα).ord (xMp - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) := by
      by_contra hle
      push_neg at hle
      have h0 : (Place.ramificationIndexAlong α V : ℤ) * (V.restrictAlong α hα).ord
          (xMp - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle
      omega
    have := ModularCurve.JHPlaceSpecialization.ord_pos_sp_sub_algebraMap_of_ord_pos p M H hpM hpM2 A hA Psp xMp xb
      (by rw [hxMp_def]) (by rw [hxb_def]) (V.restrictAlong α hα) a hre
    rw [ha] at this
    exact this
  refine ⟨E₀, C₀, fun V => by rw [hE₀]; exact le_max_right _ _, ?_, ?_, ?_, fun V => by rw [hC₀]; exact le_max_right _ _, ?_, ?_, ?_⟩
  ·
    intro V hV
    have h1 := hpin V hV
    have hnotfix : ¬ JHPlaceSpecialization.Fixed p M H hpM A δ (Psp.reduceFst α hα V) := by
      intro hfix
      apply hc_badF
      rw [hbadF]
      exact Finset.mem_image.mpr ⟨_, hFix.mem_toFinset.mpr hfix, jval_eq xb _ h1⟩
    rcases hTD V with hone | htwo
    ·
      refine Or.inr ⟨hone, fun hfix2 => hnotfix ?_⟩
      rw [hone]
      have h3 := hFixUp _ hfix2
      rw [hφ_def] at h3
      exact h3
    · exact Or.inl ⟨htwo, hnotfix⟩
  ·
    intro V hV
    have h1 := hpin V hV
    have hmemT : ∀ w ∈ T, w ∈ Tall := fun w hw => by
      rw [hTall]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hw)
    constructor
    · intro hmem
      apply hc_badT
      rw [hbadT]
      exact Finset.mem_image.mpr ⟨Psp.reduceFst α hα V, hmemT _ hmem, jval_eq xb _ h1⟩
    · intro hmem
      rcases hTD V with hone | htwo
      ·
        apply hc_badT
        rw [hbadT]
        refine Finset.mem_image.mpr ⟨Psp.reduceFst α hα V, ?_, jval_eq xb _ h1⟩
        rw [hTall, hone]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hmem, by rw [hφ_def]⟩))
      ·
        have h2 := n2 (Psp.reduceFst α hα V) c h1
        apply hc_pre
        rw [Finset.mem_preimage, frobenius_def, hbadT]
        refine Finset.mem_image.mpr ⟨φ (Psp.reduceFst α hα V), ?_, jval_eq xb _ h2⟩
        rw [hTall]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Psp.reduceSnd β hβ δ V, hmem, ?_⟩)
        rw [← htwo, hδτ, inv_smul_smul, hφ_def]
  ·
    have hdegC : 0 < Divisor.degree C₀ := by
      have hcusp : 0 < C₀ Winf := by
        rw [hC₀]
        exact lt_max_of_lt_left (by omega)
      have hmem : Winf ∈ C₀.support := Finsupp.mem_support_iff.mpr hcusp.ne'
      have hsum : Divisor.degree C₀ = ∑ v ∈ C₀.support, C₀ v := by
        show (Finsupp.liftAddHom _) C₀ = _
        rw [Finsupp.liftAddHom_apply, Finsupp.sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        show C₀ v * ((v.deg : ℕ) : ℤ) = C₀ v
        rw [hup v]
        simp
      rw [hsum]
      exact lt_of_lt_of_le hcusp (Finset.single_le_sum (fun v _ => by rw [hC₀]; exact le_max_right _ _) hmem)
    have hEC : E₀ - C₀ = Df := Finsupp.ext fun V => by
      simp only [Finsupp.coe_sub, Pi.sub_apply, hE₀, hC₀, hDf V]
      omega
    have h1 : (E₀ - C₀).degree = 0 := by rw [hEC]; exact hDfdeg
    rw [map_sub] at h1
    linarith
  ·
    intro σ _
    ext V
    rw [SemilinearAut.divisor_smul_apply, hC₀, hC₀]
    have h1 : ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)⁻¹ • V).ord f
        = V.ord ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • f) := by
      have h := SemilinearAut.ord_smul (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
        ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)⁻¹ • V) f
      rw [smul_inv_smul] at h
      exact h.symm
    have hjfix : (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • xM = xM := by
      rw [hxM_def]; exact Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact coeffMap_jqModC _)
    have h2 : (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • f
        = xM - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (σ (a : AlgebraicClosure ℚ)) := by
      rw [hf_def, SemilinearAut.smul_def, map_sub, ← SemilinearAut.smul_def,
        ← SemilinearAut.smul_def, hjfix, SemilinearAut.smul_algebraMap]
      rfl
    rw [h1, h2, negOrd_sub_algebraMap_eq, hf_def, negOrd_sub_algebraMap_eq]
  ·
    have hcusp : 0 < C₀ Winf := by
      rw [hC₀]
      exact lt_max_of_lt_left (by omega)
    have hmem : Winf ∈ C₀.support := Finsupp.mem_support_iff.mpr hcusp.ne'
    have hsum : Divisor.degree C₀ = ∑ v ∈ C₀.support, C₀ v := by
      show (Finsupp.liftAddHom _) C₀ = _
      rw [Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      show C₀ v * ((v.deg : ℕ) : ℤ) = C₀ v
      rw [hup v]
      simp
    rw [hsum]
    exact lt_of_lt_of_le hcusp (Finset.single_le_sum (fun v _ => by rw [hC₀]; exact le_max_right _ _) hmem)
  ·
    exact ⟨f, hf0, fun V => by
      simp only [Finsupp.coe_sub, Pi.sub_apply, hE₀, hC₀]
      omega⟩

end
p2m_reactivate "P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq.RREngineH"

end S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_reduce_notMem_isPrincipal_sub_of_smul_eq (solution)
