-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/44e92528-76e3-5547-a0f5-fe1cb2559c59

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

set_option maxHeartbeats 3200000

namespace D0JCor

open ModularCurve AlgebraicCurve

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have : -f = algebraMap K F (-1) * f := by rw [map_neg, map_one, neg_one_mul]
  have h1 : algebraMap K F (-1) ≠ 0 := by rw [map_neg, map_one]; exact neg_ne_zero.mpr one_ne_zero
  rw [this, v.ord_mul h1 hf, Place.ord_algebraMap, zero_add]

theorem not_ord_pos_and_ord_sub_one_pos (v : Place K F) (x : F) (h0 : 0 < v.ord x) (h1 : 0 < v.ord (x - 1)) : False := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h0
  have hx1 : x - 1 ≠ 0 := by rintro h; rw [h] at h1; simp at h1
  have hneg : -(x - 1) ≠ 0 := neg_ne_zero.mpr hx1
  have hsum : x + -(x - 1) = 1 := by ring
  have h := Place.min_ord_le_ord_add v hx0 hneg (by rw [hsum]; exact one_ne_zero)
  rw [hsum, Place.ord_one, ord_neg] at h
  have : 0 < min (v.ord x) (v.ord (x - 1)) := lt_min h0 h1
  omega

theorem max_neg_ord_sub_algebraMap (v : Place K F) (x : F) (c : K) :
    max (-v.ord (x - algebraMap K F c)) 0 = max (-v.ord x) 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_sub, ord_neg, Place.ord_algebraMap, Place.ord_zero]
  by_cases hlt : v.ord x < 0
  ·
    have h := Place.ord_add_eq_of_lt v hx (neg_ne_zero.mpr hc') (by rw [ord_neg, Place.ord_algebraMap]; exact hlt)
    rw [← sub_eq_add_neg] at h
    rw [h]
  ·
    push Not at hlt
    have h1 : max (-v.ord x) 0 = 0 := max_eq_right (by omega)
    rw [h1]
    apply max_eq_right
    rcases eq_or_ne (x - algebraMap K F c) 0 with h0 | h0
    · rw [h0, Place.ord_zero]; rfl
    · have h := Place.min_ord_le_ord_add v hx (neg_ne_zero.mpr hc') (by rw [← sub_eq_add_neg]; exact h0)
      rw [← sub_eq_add_neg, ord_neg, Place.ord_algebraMap] at h
      have : 0 ≤ min (v.ord x) 0 := le_min hlt le_rfl
      omega

theorem divisor_eq_of_forall {D D' : Divisor K F} (h : ∀ v, D v = D' v) : D = D' := Finsupp.ext h

def total {α : Type*} (D : α →₀ ℤ) : ℤ := D.sum fun _ n => n

theorem total_mapDomain {α β : Type*} (f : α → β) (D : α →₀ ℤ) : total (Finsupp.mapDomain f D) = total D := by
  unfold total
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem total_add {α : Type*} (D D' : α →₀ ℤ) : total (D + D') = total D + total D' := by
  unfold total
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem total_eq_sum_of_support_subset {α : Type*} (D : α →₀ ℤ) (S : Finset α) (hS : D.support ⊆ S) :
    total D = ∑ a ∈ S, D a := by
  classical
  unfold total
  exact Finsupp.sum_of_support_subset D hS _ (fun _ _ => rfl)

theorem eq_zero_of_nonneg_of_total_nonpos {α : Type*} (E : α →₀ ℤ) (hnn : ∀ a, 0 ≤ E a) (htot : total E ≤ 0) : E = 0 := by
  classical
  have hsum : ∑ a ∈ E.support, E a ≤ 0 := by rwa [← total_eq_sum_of_support_subset E E.support (subset_refl _)]
  have hall : ∀ a ∈ E.support, E a = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).mp (le_antisymm hsum (Finset.sum_nonneg fun a _ => hnn a))
    exact this
  ext a
  by_cases ha : a ∈ E.support
  · exact hall a ha
  · exact Finsupp.notMem_support_iff.mp ha

end Generic

theorem sub_algebraMap_ne_zero_of_coe_eq_jqModC {L : Type*} [Field L] (S : IntermediateField L (LaurentSeries L)) (y : ↥S)
    (hy : (y : LaurentSeries L) = jqModC L) (c : L) : y - algebraMap L S c ≠ 0 := by
  intro h
  have h1 : ((y - algebraMap L S c : ↥S) : LaurentSeries L) = 0 := by rw [h]; rfl
  have h2 : ((y - algebraMap L S c : ↥S) : LaurentSeries L) = jqModC L - HahnSeries.single 0 c := by
    rw [AddSubgroupClass.coe_sub, hy, SubalgebraClass.coe_algebraMap, algebraMap_laurentSeries_eq_single]
  rw [h2, sub_eq_zero] at h1
  have h3 : (jqModC L).coeff (-1) ≠ 0 := by
    have := order_jqModC_def L
    rw [← this]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr) (by intro h0; rw [h0, HahnSeries.order_zero] at this; exact absurd this (by norm_num))
  rw [h1, HahnSeries.coeff_single_of_ne (by norm_num)] at h3
  exact h3 rfl

theorem le_mapDomain_apply {α β : Type*} (f : α → β) (Z : α →₀ ℤ) (hZ : ∀ a, 0 ≤ Z a) (w : α) :
    Z w ≤ Finsupp.mapDomain f Z (f w) := by
  classical
  by_cases hw : w ∈ Z.support
  · rw [Finsupp.mapDomain, Finsupp.sum_apply]
    unfold Finsupp.sum
    have hterm : Z w = Finsupp.single (f w) (Z w) (f w) := by rw [Finsupp.single_eq_same]
    rw [hterm]
    refine Finset.single_le_sum (f := fun a => Finsupp.single (f a) (Z a) (f w)) (fun a _ => ?_) hw
    show 0 ≤ Finsupp.single (f a) (Z a) (f w)
    rw [Finsupp.single_apply]
    split_ifs
    · exact hZ a
    · exact le_rfl
  · rw [Finsupp.notMem_support_iff.mp hw]

    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    unfold Finsupp.sum
    refine Finset.sum_nonneg fun a _ => ?_
    show 0 ≤ Finsupp.single (f a) (Z a) (f w)
    rw [Finsupp.single_apply]
    split_ifs
    · exact hZ a
    · exact le_rfl

end D0JCor

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A) :
    ∀ (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
      ∀ (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (∀ a : ↥A, w.ord (x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) ≤ 0) →
        (Psp.sp w).ord xb < 0 := by
  intro x xb hx hxb w hw
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM)).1
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    IsCurveOver.hasPrincipalDivisors
  have hxc : ∀ c : AlgebraicClosure ℚ, x - algebraMap (AlgebraicClosure ℚ) _ c ≠ 0 :=
    fun c => D0JCor.sub_algebraMap_ne_zero_of_coe_eq_jqModC _ x hx c
  have hx0 : x ≠ 0 := by have := hxc 0; rwa [map_zero, sub_zero] at this

  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hx0
  let Pl : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := (-D₀) ⊔ 0
  have hPl : ∀ v, Pl v = max (-v.ord x) 0 := by
    intro v; show ((-D₀) ⊔ 0) v = _; rw [Finsupp.sup_apply, Finsupp.neg_apply, hD₀ v]; rfl
  have hPlnn : ∀ v, 0 ≤ Pl v := fun v => by rw [hPl]; exact le_max_right _ _
  have hE2 := (ModularCurve.JHPlaceSpecialization.mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC
    p M H hpM hpM2 A hA Psp x xb hx hxb).2 Pl hPl (Psp.sp w)

  suffices hsuff : 0 < Finsupp.mapDomain Psp.sp Pl (Psp.sp w) by
    rw [hE2] at hsuff
    rcases lt_max_iff.mp hsuff with h | h
    · omega
    · exact absurd h (lt_irrefl 0)
  by_cases hpole : w.ord x < 0
  ·
    have hw1 : 0 < Pl w := by rw [hPl]; exact lt_max_of_lt_left (by omega)
    exact lt_of_lt_of_le hw1 (D0JCor.le_mapDomain_apply Psp.sp Pl hPlnn w)
  ·
    push_neg at hpole
    have hwrat : w.IsRational := (AlgebraicCurve.Place.isRational_iff_deg_eq_one w).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed w)
    have hmem : x ∈ w.toValuationSubring := w.mem_toValuationSubring_of_ord_nonneg_alt hx0 hpole
    set b : AlgebraicClosure ℚ := w.evalAt x with hbdef
    have hb : 0 < w.ord (x - algebraMap (AlgebraicClosure ℚ) _ b) :=
      (AlgebraicCurve.Place.mem_and_evalAt_eq_iff_ord_sub_algebraMap_pos w hwrat x b
        (fun h => hxc b (sub_eq_zero.mpr h))).mp ⟨hmem, rfl⟩
    have hbA : b ∉ A := fun hbA => absurd hb (not_lt.mpr (hw ⟨b, hbA⟩))
    have hb0 : b ≠ 0 := fun h => hbA (h ▸ A.zero_mem)
    have hcA : b⁻¹ ∈ A := (A.mem_or_inv_mem b).resolve_left hbA
    let c : ↥A := ⟨b⁻¹, hcA⟩
    have hcb : (c : AlgebraicClosure ℚ) * b = 1 := inv_mul_cancel₀ hb0
    have hcres : IsLocalRing.residue ↥A c = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      by_contra hcu
      have hu : IsUnit c := by
        by_contra hnu; exact hcu ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      obtain ⟨u, hu⟩ := hu
      apply hbA
      have : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = b := by
        have h1 : ((u : ↥A) : AlgebraicClosure ℚ) * ((u⁻¹ : (↥A)ˣ) : ↥A) = 1 := by
          rw [← Subring.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        have h2 : (c : AlgebraicClosure ℚ) = b⁻¹ := rfl
        rw [h2] at h1
        calc ((u⁻¹ : (↥A)ˣ) : ↥A).1 = b * (b⁻¹ * ((u⁻¹ : (↥A)ˣ) : ↥A).1) := by rw [← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
          _ = b := by rw [h1, mul_one]
      rw [← this]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
    have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := inv_ne_zero hb0

    let f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := 1 - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ) * x
    let y : LaurentSeries ↥A := 1 - HahnSeries.single 0 c * jqModC ↥A
    have hy : coeffMap A.subtype y = ((f : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      show coeffMap A.subtype (1 - HahnSeries.single 0 c * jqModC ↥A) =
        (((1 - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ) * x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) : LaurentSeries (AlgebraicClosure ℚ))
      rw [map_sub, map_one, map_mul, coeffMap_single, coeffMap_jqModC, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
        MulMemClass.coe_mul, hx, SubalgebraClass.coe_algebraMap, algebraMap_laurentSeries_eq_single]
      rfl
    have hg : (((1 : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        coeffMap (IsLocalRing.residue ↥A) y := by
      show _ = coeffMap (IsLocalRing.residue ↥A) (1 - HahnSeries.single 0 c * jqModC ↥A)
      rw [map_sub, map_one, map_mul, coeffMap_single, hcres, HahnSeries.single_eq_zero, zero_mul, sub_zero, OneMemClass.coe_one]

    have hfeq : f = algebraMap (AlgebraicClosure ℚ) _ (-(c : AlgebraicClosure ℚ)) * (x - algebraMap (AlgebraicClosure ℚ) _ b) := by
      show 1 - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ) * x = _
      rw [mul_sub, ← map_mul, neg_mul, hcb, map_neg _ (1 : AlgebraicClosure ℚ), map_one, map_neg]; ring
    have hf0 : f ≠ 0 := by
      rw [hfeq]; exact mul_ne_zero ((map_ne_zero _).mpr (neg_ne_zero.mpr hc0)) (hxc b)
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
    have hDord : ∀ v, D v = v.ord (x - algebraMap (AlgebraicClosure ℚ) _ b) := by
      intro v
      rw [hD v, hfeq, AlgebraicCurve.Place.ord_mul _ ((map_ne_zero _).mpr (neg_ne_zero.mpr hc0)) (hxc b),
        AlgebraicCurve.Place.ord_algebraMap, zero_add]

    have hq := Psp.d0_qexp f y hy 1 hg one_ne_zero D hD (Psp.sp w)
    rw [AlgebraicCurve.Place.ord_one] at hq

    obtain ⟨Db, hDb, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ (hxc b)
    let Zb : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Db ⊔ 0
    have hZb : ∀ v, Zb v = max (v.ord (x - algebraMap (AlgebraicClosure ℚ) _ b)) 0 := by
      intro v; show (Db ⊔ 0) v = _; rw [Finsupp.sup_apply, hDb v]; rfl
    have hZbnn : ∀ v, 0 ≤ Zb v := fun v => by rw [hZb]; exact le_max_right _ _
    have hDeq : D = Zb - Pl := by
      ext v
      rw [Finsupp.sub_apply, hDord, hZb, hPl, ← D0JCor.max_neg_ord_sub_algebraMap v x b]
      omega
    rw [hDeq, Finsupp.mapDomain_sub, Finsupp.sub_apply] at hq
    have hZw : 0 < Zb w := by rw [hZb]; exact lt_max_of_lt_left hb
    have := D0JCor.le_mapDomain_apply Psp.sp Zb hZbnn w
    omega

end S_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le (solution)
