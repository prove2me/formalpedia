-- Prove2me | solution 1 for ModularCurve.FullLevel.mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/12f5c193-39b6-5082-9962-cd16426734f1

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ModularPolynomialData_evalSymm_of_one_lt
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ValuationSubring_forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "FullLevel.levelH FullLevel.fieldBar x0_le_xHFunctionFieldC qExpFunctionFieldC modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_C qExpand_one_apply constantCoeff_jNum jq jqN evalAtJ evalAtJ_X ModularPolynomialData modularFunctionFieldFull jqd_mem_full full_degeneracy_le full_degeneracy_map_le coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC map_jqModC modularFunctionFieldC transcendental_jqModC qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull ModularPolynomialData.evalSymm_of_one_lt exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC nonempty_modularPolynomialData finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0 transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC"
p2m_open "ModularCurve~coeffMap_qExpand"

namespace KSharpPin

open HahnSeries IntermediateField AlgebraicCurve IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

section Coeff

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem coeffMap_subtype_injective : Function.Injective (coeffMap A.subtype) := by
  intro x y h
  ext k
  have hk := congrArg (fun z : LaurentSeries L => z.coeff k) h
  simp only [coeffMap_coeff] at hk
  exact hk

theorem coeffMap_subtype_ne_zero {x : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) : coeffMap A.subtype x ≠ 0 := by
  intro h
  apply hx
  have hx0 : x = 0 := coeffMap_subtype_injective A (by rw [h, map_zero])
  rw [hx0, map_zero]

theorem ne_zero_of_residue_ne_zero {x : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact hx (map_zero _)

theorem residue_mul_ne_zero {x y : LaurentSeries A}
    (hx : coeffMap (IsLocalRing.residue A) x ≠ 0) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0) :
    coeffMap (IsLocalRing.residue A) (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

theorem coeffMap_subtype_C (a : A) : coeffMap A.subtype (HahnSeries.C a) = HahnSeries.C (a : L) :=
  coeffMap_C _ _

theorem algebraMap_eq_C (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

end Coeff

section ConstantAction

variable (L : Type*) [Field L]

theorem coe_smul_eq_C_mul (F : IntermediateField L (LaurentSeries L)) (c : L) (x : F) :
    ((c • x : F) : LaurentSeries L) = HahnSeries.C c * (x : LaurentSeries L) := by
  rw [@Algebra.smul_def L F _ _ (SubalgebraClass.toAlgebra F), MulMemClass.coe_mul,
    SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

theorem coe_algebraMap_eq_C (F : IntermediateField L (LaurentSeries L)) (c : L) :
    ((algebraMap L F c : F) : LaurentSeries L) = HahnSeries.C c := by
  rw [SubalgebraClass.coe_algebraMap, algebraMap_eq_C]

theorem C_mem (F : IntermediateField L (LaurentSeries L)) (c : L) : HahnSeries.C c ∈ F := by
  rw [← algebraMap_eq_C]
  exact F.algebraMap_mem c

end ConstantAction

section Sharp

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem coeffEmb_qExpand' (N : ℕ) [NeZero N] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ N x) = qExpand L N (coeffEmb L x) :=
  coeffMap_qExpand _ N x

theorem laurentBaseChange_mono {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ :=
  IntermediateField.adjoin.mono L _ _ (Set.image_mono h)

theorem qExpand_mem_laurentBaseChange {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (N : ℕ) [NeZero N]
    (h : ∀ s : LaurentSeries ℚ, s ∈ F₀ → qExpand ℚ N s ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L N x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_eq_C, qExpand_C]
        exact C_mem L _ a
      · rw [← coeffEmb_qExpand']
        exact coeffEmb_mem_laurentBaseChange L (h z hz)
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem qExpand_mem_fieldBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    {g : LaurentSeries (AlgebraicClosure ℚ)}
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    qExpand (AlgebraicClosure ℚ) q g ∈ FullLevel.fieldBar q M' := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero (M' * q) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne q)⟩
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (NeZero.ne q)) (NeZero.ne M')⟩
  have step : qExpand (AlgebraicClosure ℚ) q g ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 (q ^ 2 * M'))) := by
    refine qExpand_mem_laurentBaseChange (AlgebraicClosure ℚ) q ?_ hg
    intro s hs
    rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull] at hs ⊢
    have h1 : qExpand ℚ q s ∈ modularFunctionFieldFull (M' * q) := by
      refine full_degeneracy_map_le M' q ?_
      exact ⟨s, hs, rfl⟩
    exact full_degeneracy_le ⟨q, by ring⟩ h1
  exact laurentBaseChange_mono (AlgebraicClosure ℚ)
    (x0_le_xHFunctionFieldC ℚ (q ^ 2 * M') (FullLevel.levelH q M')) step

def iotaSharp (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))) →+*
      ↥(FullLevel.fieldBar q M') :=
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  { toFun := fun g => ⟨qExpand (AlgebraicClosure ℚ) q (g : LaurentSeries (AlgebraicClosure ℚ)),
      qExpand_mem_fieldBar q M' g.2⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun a b => Subtype.ext (by simp)
    map_zero' := Subtype.ext (by simp)
    map_add' := fun a b => Subtype.ext (by simp) }

theorem coe_iotaSharp (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (g : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))) :
    ((iotaSharp q M' g : ↥(FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      @qExpand _ _ q ⟨(Fact.out : q.Prime).ne_zero⟩ (g : LaurentSeries (AlgebraicClosure ℚ)) := rfl

end Sharp

section JSeries

variable {K : Type*} [Field K]

theorem coeff_neg_one_jqModC : (jqModC K).coeff (-1) = 1 := by
  have h : (jqModC K).coeff (0 + (-1)) = 1 := by
    simp only [jqModC, HahnSeries.coeff_single_mul_add, one_mul]
    rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
  simpa using h

theorem jqModC_ne_C (c : K) : jqModC K ≠ HahnSeries.C c := by
  intro h
  have := congrArg (fun z : LaurentSeries K => z.coeff (-1)) h
  simp only [coeff_neg_one_jqModC, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide)]
    at this
  exact one_ne_zero this

theorem transcendental_jqModC [IsAlgClosed K] : Transcendental K (jqModC K) := by
  intro halg
  have hint : IsIntegral K (jqModC K) := halg.isIntegral
  have hirr : Irreducible (minpoly K (jqModC K)) := minpoly.irreducible hint
  have hdeg : (minpoly K (jqModC K)).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K hirr
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K (jqModC K) hdeg
  exact jqModC_ne_C c (by rw [← hc, algebraMap_eq_C])

theorem aeval_jqModC_ne_zero [IsAlgClosed K] {P : Polynomial K} (hP : P ≠ 0) :
    Polynomial.aeval (jqModC K) P ≠ 0 := fun h =>
  hP ((transcendental_iff.mp transcendental_jqModC) P h)

end JSeries

section Generic

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem isUnit_iff_inv_mem {F : Type*} [Field F] (S : ValuationSubring F) (x : ↥S) :
    IsUnit x ↔ (x : F) ≠ 0 ∧ (x : F)⁻¹ ∈ S := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : ↥S) : F) * ((↑u⁻¹ : ↥S) : F) = 1 := by
      exact congrArg Subtype.val u.mul_inv
    have hne : ((u : ↥S) : F) ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
    refine ⟨hne, ?_⟩
    rw [show ((u : ↥S) : F)⁻¹ = ((↑u⁻¹ : ↥S) : F) from (eq_inv_of_mul_eq_one_right h1).symm]
    exact (↑u⁻¹ : ↥S).2
  · rintro ⟨hne, hinv⟩
    exact ⟨⟨x, ⟨(x : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

theorem map_mem_nonunits_of_mem_maximalIdeal {F : Type*} [Field F] (φ : L →+* F) (V : ValuationSubring F)
    (hV : ∀ c : L, φ c ∈ V ↔ c ∈ A) (a : ↥A) (ha : a ∈ maximalIdeal ↥A) : φ (a : L) ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨(hV _).mpr a.2, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_inv_mem]
  rintro ⟨hne, hinv⟩
  have ha0 : (a : L) ≠ 0 := by
    rintro h; apply hne
    show φ (a : L) = 0
    rw [h, map_zero]
  have hinvA : (a : L)⁻¹ ∈ A := (hV _).mp (by rw [map_inv₀]; exact hinv)
  have hunit : IsUnit a :=
    ⟨⟨a, ⟨(a : L)⁻¹, hinvA⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩
  exact (IsLocalRing.mem_maximalIdeal a).mp ha hunit

theorem mem_iff_const_mem_of_rel {F : Type*} [Field F] (φ : L →+* F) (V : ValuationSubring F)
    (hV : ∀ c : L, φ c ∈ V ↔ c ∈ A)
    (e X Y : F) {c : L} (hX0 : X ≠ 0) (hY0 : Y ≠ 0)
    (hXV : X ∈ V) (hXinv : X⁻¹ ∈ V) (hYV : Y ∈ V) (hYinv : Y⁻¹ ∈ V)
    (hrel : e * Y = φ c * X) : e ∈ V ↔ c ∈ A := by
  rw [← hV c]
  constructor
  · intro heV
    have h : φ c = e * Y * X⁻¹ := by rw [hrel, mul_inv_cancel_right₀ hX0]
    rw [h]
    exact mul_mem (mul_mem heV hYV) hXinv
  · intro hcV
    have h : e = φ c * X * Y⁻¹ := by rw [← hrel, mul_inv_cancel_right₀ hY0]
    rw [h]
    exact mul_mem (mul_mem hcV hXV) hYinv

theorem exists_eq_smul_map (N : Polynomial L) (hN : N ≠ 0) :
    ∃ (c : L) (P : Polynomial ↥A), c ≠ 0 ∧ P.map (IsLocalRing.residue ↥A) ≠ 0 ∧ N = c • P.map A.subtype := by
  classical
  have hne : N.support.Nonempty := Polynomial.support_nonempty.mpr hN
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image N.support (fun i => A.valuation (N.coeff i)) hne
  set c := N.coeff i₀ with hc
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀

  have hcoef : ∀ i, (c⁻¹ • N).coeff i ∈ A := by
    intro i
    rw [Polynomial.coeff_smul, smul_eq_mul]
    by_cases hi : i ∈ N.support
    · rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
      have hle := hmax i hi
      have hcv : A.valuation c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
      calc (A.valuation c)⁻¹ * A.valuation (N.coeff i)
          ≤ (A.valuation c)⁻¹ * A.valuation c := by gcongr
        _ = 1 := inv_mul_cancel₀ hcv
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]; exact zero_mem _
  have hsub : (↑(c⁻¹ • N).coeffs : Set L) ⊆ A.toSubring := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := (Polynomial.mem_coeffs_iff).mp hx
    exact hcoef n
  refine ⟨c, (c⁻¹ • N).toSubring A.toSubring hsub, hc0, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun P : Polynomial (ResidueField ↥A) => P.coeff i₀) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
    have h2 : ((c⁻¹ • N).coeff i₀) = 1 := by
      rw [Polynomial.coeff_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hc0]
    have h3 : ((c⁻¹ • N).toSubring A.toSubring hsub).coeff i₀ = 1 := by
      apply Subtype.ext
      rw [Polynomial.coeff_toSubring]
      exact h2
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  · have hmap : ((c⁻¹ • N).toSubring A.toSubring hsub).map A.subtype = c⁻¹ • N :=
      Polynomial.map_toSubring _ _ _
    rw [hmap, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end Generic

section Gauss

variable {L : Type*} [Field L] (A : ValuationSubring L) (F : IntermediateField L (LaurentSeries L))

theorem gauss_const_mem_iff (V : ValuationSubring ↥F)
    (hV : ∀ f : ↥F, f ∈ V ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x)
    (c : L) : algebraMap L (↥F) c ∈ V ↔ c ∈ A := by
  rw [hV, coe_algebraMap_eq_C]
  constructor
  · rintro ⟨x, y, hy, hxy⟩

    have : ∃ n, (IsLocalRing.residue ↥A) (y.coeff n) ≠ 0 := by
      by_contra h
      push Not at h
      apply hy
      ext n
      rw [coeffMap_coeff, h n, HahnSeries.coeff_zero]
    obtain ⟨n, hn⟩ := this
    have hu : IsUnit (y.coeff n) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
    have hcoeff := congrArg (fun z : LaurentSeries L => z.coeff n) hxy
    simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul] at hcoeff
    change c * ((y.coeff n : ↥A) : L) = ((x.coeff n : ↥A) : L) at hcoeff

    have hyn0 : ((y.coeff n : ↥A) : L) ≠ 0 := by
      intro h0; apply hu.ne_zero; exact Subtype.ext h0
    have hc : c = (x.coeff n : L) * ((y.coeff n : ↥A) : L)⁻¹ := by
      rw [← hcoeff, mul_inv_cancel_right₀ hyn0]
    rw [hc]
    refine mul_mem (x.coeff n).2 ?_
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', show (((u : ↥A)) : L)⁻¹ = ((↑u⁻¹ : ↥A) : L) from ?_]
    · exact (↑u⁻¹ : ↥A).2
    · symm; apply eq_inv_of_mul_eq_one_right
      exact congrArg Subtype.val u.mul_inv
  · intro hc
    refine ⟨HahnSeries.C ⟨c, hc⟩, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one, coeffMap_subtype_C]

theorem eval₂_mem (f : ↥A →+* LaurentSeries L) (hf : ∀ a, f a ∈ F) {x : LaurentSeries L} (hx : x ∈ F)
    (P : Polynomial ↥A) : P.eval₂ f x ∈ F := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact add_mem hp hq
  | monomial n a =>
      rw [Polynomial.eval₂_monomial]
      exact mul_mem (hf a) (pow_mem hx n)

theorem coeffMap_subtype_eval₂_C_jqModC (P : Polynomial ↥A) :
    coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) =
      P.eval₂ ((HahnSeries.C : L →+* LaurentSeries L).comp A.subtype) (jqModC L) := by
  have hj : coeffMap A.subtype (jqModC ↥A) = jqModC L := map_jqModC _
  rw [Polynomial.hom_eval₂, hj]
  congr 1
  ext a : 1
  show coeffMap A.subtype (HahnSeries.C a) = HahnSeries.C (a : L)
  exact coeffMap_subtype_C A a

theorem coeffMap_residue_eval₂_C_jqModC (P : Polynomial ↥A) :
    coeffMap (IsLocalRing.residue ↥A) (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) =
      Polynomial.aeval (jqModC (ResidueField ↥A)) (P.map (IsLocalRing.residue ↥A)) := by
  have hj : coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := map_jqModC _
  rw [Polynomial.hom_eval₂, hj, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  ext a : 1
  show coeffMap (IsLocalRing.residue ↥A) (HahnSeries.C a) = algebraMap _ _ ((IsLocalRing.residue ↥A) a)
  rw [coeffMap_C, algebraMap_eq_C]

end Gauss

section Roots

variable (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))

theorem isRoot_map_eval₂RingHom_of_coe (Φ : Polynomial (Polynomial ℤ)) (J J' : ↥F)
    (h : Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
      (J : LaurentSeries (AlgebraicClosure ℚ))) (J' : LaurentSeries (AlgebraicClosure ℚ)) = 0) :
    (Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥F) J)).IsRoot J' := by
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  apply Subtype.val_injective
  have key := Polynomial.hom_eval₂ Φ (Polynomial.eval₂RingHom (Int.castRingHom ↥F) J) F.val.toRingHom J'
  have hcomp : F.val.toRingHom.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥F) J) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
        (J : LaurentSeries (AlgebraicClosure ℚ)) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  rw [hcomp] at key
  show F.val.toRingHom (Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥F) J) J') = (0 : ↥F).val
  rw [key]
  exact h

theorem eval₂_modularPolynomial_jq_jqq (q : ℕ) [NeZero q] (data : ModularPolynomialData q) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
      (jqModC (AlgebraicClosure ℚ))) (qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ))) = 0 := by
  have hjemb : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have e0 := data.eval_eq_zero
  have key := Polynomial.hom_eval₂ data.Φ evalAtJ (coeffEmb (AlgebraicClosure ℚ)) (jqN q)
  rw [e0, map_zero] at key
  have hcomp : (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)) := by
    apply Polynomial.ringHom_ext
    · intro a; simp [evalAtJ]
    · simp only [RingHom.coe_comp, Function.comp_apply, evalAtJ_X, Polynomial.eval₂RingHom]
      simp [hjemb]
  have hN : coeffEmb (AlgebraicClosure ℚ) (jqN q) = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) := by
    rw [show jqN q = qExpand ℚ q jq from rfl, coeffEmb_qExpand', hjemb]
  rw [hcomp, hN] at key
  exact key.symm

theorem eval₂_modularPolynomial_jqq_jq (q : ℕ) [NeZero q] (hq : 1 < q) (data : ModularPolynomialData q) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
      (qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)))) (jqModC (AlgebraicClosure ℚ)) = 0 := by
  have hjemb : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have hsymm := ModularCurve.ModularPolynomialData.evalSymm_of_one_lt q hq data jq (jqN q)
  have hev : (Polynomial.aeval (R := ℤ) jq).toRingHom = evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [evalAtJ]
    · simp [evalAtJ_X]
  rw [hev, data.eval_eq_zero] at hsymm

  have key := Polynomial.hom_eval₂ data.Φ (Polynomial.aeval (R := ℤ) (jqN q)).toRingHom
    (coeffEmb (AlgebraicClosure ℚ)) jq
  rw [← hsymm, map_zero] at key
  have hcomp : (coeffEmb (AlgebraicClosure ℚ)).comp (Polynomial.aeval (R := ℤ) (jqN q)).toRingHom =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ)))
        (qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ))) := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.eval₂RingHom]
      simp [show jqN q = qExpand ℚ q jq from rfl, coeffEmb_qExpand', hjemb]
  rw [hcomp, hjemb] at key
  exact key.symm

end Roots

end KSharpPin

end ModularCurve

end

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand P2MW.S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem.ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (O : ValuationSubring (fieldBar q M'))
    (hOA : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A)
    (hOR₀ : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ O)
    (x : fieldBar q M') (g : LaurentSeries (AlgebraicClosure ℚ))
    (hg : g ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')))
    (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) q g) :
    x ∈ O ↔ x ∈ OIg (lineInfty q) := by
  classical

  let Qb := AlgebraicClosure ℚ
  let K0 : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
    laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))
  let F := fieldBar q M'
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq1 : 1 < q := by omega
  have hT : ModularGroup.T ∈ Gamma0 M' := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  haveI hκ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A

  obtain ⟨R, hRmem, hRpin⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A
      (Gamma0 M') hT
  have hjeq : coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have hjemb : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have hjfull : jq ∈ modularFunctionFieldFull M' := by
    have h := jqd_mem_full M' (one_dvd M'); rwa [qExpand_one_apply] at h
  have hjK0 : coeffMap A.subtype (jqModC ↥A) ∈ K0 := by
    show _ ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M'))
    rw [hjeq, ← hjemb, qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact coeffEmb_mem_laurentBaseChange _ hjfull
  have hjBar : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hjeq, ← hjemb]; exact coeffEmb_mem_laurentBaseChange _ hjfull
  obtain ⟨hjbO, hjbres⟩ := hRpin (jqModC ↥A) hjK0
  set jb : ↥K0 := ⟨coeffMap A.subtype (jqModC ↥A), hjK0⟩ with hjb_def
  have hjbres' : ((R.residue ⟨jb, hjbO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M'))) :
      LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    rw [hjbres]; exact map_jqModC _
  set J0 : ↥(modularFunctionFieldBar M') := ⟨coeffMap A.subtype (jqModC ↥A), hjBar⟩ with hJ0_def
  set J : ↥(fieldBar q M') := IntermediateField.inclusion hle J0 with hJ_def
  set J' : ↥(fieldBar q M') := ModularCurve.KSharpPin.iotaSharp q M' jb with hJ'_def
  have hJcoe : (J : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := hjeq
  have hJ'coe : (J' : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) := by
    rw [← hjeq]; rfl

  have hjbT : Transcendental (AlgebraicClosure ℚ) jb :=
    (ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      (AlgebraicClosure ℚ) (Gamma0 M') hT jb hjeq).1
  have hjresT : Transcendental (ResidueField ↥A) (R.residue ⟨jb, hjbO⟩) := by
    rw [← transcendental_algebraMap_iff
      (show Function.Injective (algebraMap ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M'))
        (LaurentSeries (ResidueField ↥A))) from Subtype.val_injective)]
    show Transcendental (ResidueField ↥A)
      ((R.residue ⟨jb, hjbO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M'))) : LaurentSeries (ResidueField ↥A))
    rw [hjbres']
    exact ModularCurve.KSharpPin.transcendental_jqModC

  have hM'κ : ((M' : ℕ) : ResidueField ↥A) ≠ 0 := by
    have h := ValuationSubring.residue_intCast_ne_zero (Fact.out : q.Prime) hA (n := (M' : ℤ))
      (by exact_mod_cast hqM')
    simpa using h
  have hΓ₁ : Gamma1 M' ≤ Gamma0 M' := by
    intro γ hγ; rw [Gamma0_mem]; exact ((Gamma1_mem M' γ).mp hγ).2.2
  have hdeg0 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gamma0_eq_index
    (AlgebraicClosure ℚ) M' jb hjeq
  have hdegκ := ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_eq_index_of_gamma1_le_of_le_gamma0
    (ResidueField ↥A) M' hM'κ (Gamma0 M') hΓ₁ le_rfl (R.residue ⟨jb, hjbO⟩) hjbres'
  have hdeg : Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jb : ↥K0)} : Set ↥K0)) ↥K0 =
      Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A)
        ({R.residue ⟨jb, hjbO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M'))))
        ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M')) := by
    rw [hdeg0, hdegκ]
  have hfin : 0 < Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A)
        ({R.residue ⟨jb, hjbO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M'))))
        ↥(qExpFunctionFieldC (ResidueField ↥A) (Gamma0 M')) := by
    rw [hdegκ]
    haveI : (Gamma0 M' ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).FiniteIndex :=
      Subgroup.finiteIndex_of_le le_sup_left
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData q
  have hΦJ : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(fieldBar q M')) J)).IsRoot J' := by
    apply ModularCurve.KSharpPin.isRoot_map_eval₂RingHom_of_coe
    rw [hJcoe, hJ'coe]
    exact ModularCurve.KSharpPin.eval₂_modularPolynomial_jq_jqq q data
  have hΨJ : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(fieldBar q M')) J')).IsRoot J := by
    apply ModularCurve.KSharpPin.isRoot_map_eval₂RingHom_of_coe
    rw [hJcoe, hJ'coe]
    exact ModularCurve.KSharpPin.eval₂_modularPolynomial_jqq_jq q hq1 data

  letI algF : Algebra ↥A ↥(fieldBar q M') := ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp A.subtype).toAlgebra
  letI algK : Algebra ↥A ↥K0 := ((algebraMap (AlgebraicClosure ℚ) ↥K0).comp A.subtype).toAlgebra
  have halgF : ∀ a : ↥A, algebraMap ↥A ↥(fieldBar q M') a = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ) :=
    fun a => rfl
  have halgK : ∀ a : ↥A, algebraMap ↥A ↥K0 a = algebraMap (AlgebraicClosure ℚ) ↥K0 (a : AlgebraicClosure ℚ) :=
    fun a => rfl

  have hPser : ∀ P : Polynomial ↥A,
      ((Polynomial.aeval J P : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) := by
    intro P
    rw [ModularCurve.KSharpPin.coeffMap_subtype_eval₂_C_jqModC, Polynomial.aeval_def,
      show ((Polynomial.eval₂ (algebraMap ↥A ↥(fieldBar q M')) J P : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))
        = (fieldBar q M').val.toRingHom (Polynomial.eval₂ (algebraMap ↥A ↥(fieldBar q M')) J P) from rfl,
      Polynomial.hom_eval₂, ← hJcoe]
    congr 1
    ext a : 1
    show ((algebraMap ↥A ↥(fieldBar q M') a : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C (a : AlgebraicClosure ℚ)
    rw [halgF, ModularCurve.KSharpPin.coe_algebraMap_eq_C]
  have hPserK : ∀ P : Polynomial ↥A,
      ((Polynomial.aeval jb P : ↥K0) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) := by
    intro P
    rw [ModularCurve.KSharpPin.coeffMap_subtype_eval₂_C_jqModC, Polynomial.aeval_def,
      show ((Polynomial.eval₂ (algebraMap ↥A ↥K0) jb P : ↥K0) : LaurentSeries (AlgebraicClosure ℚ))
        = K0.val.toRingHom (Polynomial.eval₂ (algebraMap ↥A ↥K0) jb P) from rfl,
      Polynomial.hom_eval₂, ← hjeq]
    congr 1
    ext a : 1
    show ((algebraMap ↥A ↥K0 a : ↥K0) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C (a : AlgebraicClosure ℚ)
    rw [halgK, ModularCurve.KSharpPin.coe_algebraMap_eq_C]
  have hPmemBar : ∀ P : Polynomial ↥A,
      coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) ∈ modularFunctionFieldBar M' := by
    intro P
    rw [ModularCurve.KSharpPin.coeffMap_subtype_eval₂_C_jqModC]
    refine ModularCurve.KSharpPin.eval₂_mem A (modularFunctionFieldBar M') _ (fun a => ?_) ?_ P
    · exact ModularCurve.KSharpPin.C_mem _ _ _
    · rw [← hjeq]; exact hjBar
  have hPres : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      coeffMap (IsLocalRing.residue ↥A) (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) ≠ 0 := by
    intro P hP
    rw [ModularCurve.KSharpPin.coeffMap_residue_eval₂_C_jqModC]
    exact ModularCurve.KSharpPin.aeval_jqModC_ne_zero hP

  have hgenO : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval J P ∈ O ∧ (Polynomial.aeval J P)⁻¹ ∈ O := by
    intro P hP
    obtain ⟨h0, hres⟩ := hR₀ _ (hPmemBar P)
    set z : ↥(modularFunctionFieldBar M') := ⟨_, hPmemBar P⟩ with hz
    have hres_ne : R₀.residue ⟨z, h0⟩ ≠ 0 := by
      intro h
      apply hPres P hP
      rw [← hres, h]
      rfl
    have hunit : IsUnit (⟨z, h0⟩ : ↥R₀.integers) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ← R₀.ker_residue, RingHom.mem_ker]
      exact hres_ne
    obtain ⟨hz0, hzinv⟩ := (ModularCurve.KSharpPin.isUnit_iff_inv_mem _ _).mp hunit
    have hJP : Polynomial.aeval J P = IntermediateField.inclusion hle z := Subtype.ext (hPser P)
    refine ⟨?_, ?_⟩
    · rw [hJP]; exact hOR₀ z h0
    · rw [hJP, ← map_inv₀]; exact hOR₀ z⁻¹ hzinv

  have hgenI : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval J P ∈ OIg (lineInfty q) ∧ (Polynomial.aeval J P)⁻¹ ∈ OIg (lineInfty q) := by
    intro P hP
    have hne : coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) ≠ 0 :=
      ModularCurve.KSharpPin.coeffMap_subtype_ne_zero A (hPres P hP)
    refine ⟨(hIg_inf _).mpr ⟨P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A), 1,
        by rw [map_one]; exact one_ne_zero, ?_⟩,
      (hIg_inf _).mpr ⟨1, P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A), hPres P hP, ?_⟩⟩
    · rw [map_one, mul_one, hPser]
    · have hcoe : (((Polynomial.aeval J P)⁻¹ : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
          (((Polynomial.aeval J P) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := rfl
      rw [hcoe, hPser, inv_mul_cancel₀ hne, map_one]

  have hconstI : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ OIg (lineInfty q) ↔ c ∈ A :=
    ModularCurve.KSharpPin.gauss_const_mem_iff A (fieldBar q M') (OIg (lineInfty q)) hIg_inf
  have hgenO' := ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot ↥A ↥(fieldBar q M') O
    (fun a => (hOA _).mpr a.2)
    (fun a ha => ModularCurve.KSharpPin.map_mem_nonunits_of_mem_maximalIdeal A (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) O hOA a ha)
    J J' data.Φ data.monic hΦJ data.Φ data.monic hΨJ hgenO
  have hgenI' := ValuationSubring.forall_aeval_mem_and_inv_mem_of_isRoot_of_isRoot ↥A ↥(fieldBar q M') (OIg (lineInfty q))
    (fun a => (hconstI _).mpr a.2)
    (fun a ha => ModularCurve.KSharpPin.map_mem_nonunits_of_mem_maximalIdeal A (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) (OIg (lineInfty q)) hconstI a ha)
    J J' data.Φ data.monic hΦJ data.Φ data.monic hΨJ hgenI

  have hιalg : ∀ c : AlgebraicClosure ℚ, ModularCurve.KSharpPin.iotaSharp q M' (algebraMap (AlgebraicClosure ℚ) ↥K0 c) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c := by
    intro c
    apply Subtype.ext
    rw [ModularCurve.KSharpPin.coe_iotaSharp, ModularCurve.KSharpPin.coe_algebraMap_eq_C,
      ModularCurve.KSharpPin.coe_algebraMap_eq_C, qExpand_C]
  have hιaeval : ∀ P : Polynomial ↥A, ModularCurve.KSharpPin.iotaSharp q M' (Polynomial.aeval jb P) = Polynomial.aeval J' P := by
    intro P
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
    congr 1
    ext a : 1
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [halgK, halgF, hιalg]
  have hV_of : ∀ V : ValuationSubring ↥(fieldBar q M'),
      (∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ V ↔ c ∈ A) →
      (∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
        Polynomial.aeval J' P ∈ V ∧ (Polynomial.aeval J' P)⁻¹ ∈ V) →
      ∀ e : ↥K0, e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({(jb : ↥K0)} : Set ↥K0) →
        (e ∈ V.comap (ModularCurve.KSharpPin.iotaSharp q M') ↔ e ∈ R.integers) := by
    intro V hVc hVgen e he
    rw [IntermediateField.mem_adjoin_simple_iff] at he
    obtain ⟨r, s, rfl⟩ := he
    rw [ValuationSubring.mem_comap]

    by_cases hr : r = 0
    · subst hr; simp
    by_cases hs : s = 0
    · subst hs; simp
    obtain ⟨cr, P, hcr, hP, hrP⟩ := ModularCurve.KSharpPin.exists_eq_smul_map A r hr
    obtain ⟨cs, Q, hcs, hQ, hsQ⟩ := ModularCurve.KSharpPin.exists_eq_smul_map A s hs
    have hmapaeval : ∀ P : Polynomial ↥A, Polynomial.aeval jb (P.map A.subtype) = Polynomial.aeval jb P := fun P => by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]; rfl
    have haevr : Polynomial.aeval jb r = algebraMap (AlgebraicClosure ℚ) ↥K0 cr * Polynomial.aeval jb P := by
      rw [hrP, map_smul, Algebra.smul_def, hmapaeval]
    have haevs : Polynomial.aeval jb s = algebraMap (AlgebraicClosure ℚ) ↥K0 cs * Polynomial.aeval jb Q := by
      rw [hsQ, map_smul, Algebra.smul_def, hmapaeval]

    have hPne : (Polynomial.aeval jb P : ↥K0) ≠ 0 := by
      intro h
      apply ModularCurve.KSharpPin.coeffMap_subtype_ne_zero A (hPres P hP)
      rw [← hPserK, h]; rfl
    have hQne : (Polynomial.aeval jb Q : ↥K0) ≠ 0 := by
      intro h
      apply ModularCurve.KSharpPin.coeffMap_subtype_ne_zero A (hPres Q hQ)
      rw [← hPserK, h]; rfl
    have hcsK : algebraMap (AlgebraicClosure ℚ) ↥K0 cs ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥K0).injective]; exact hcs

    set e : ↥K0 := Polynomial.aeval jb r / Polynomial.aeval jb s with he_def
    have hrel : e * Polynomial.aeval jb Q = algebraMap (AlgebraicClosure ℚ) ↥K0 (cr / cs) * Polynomial.aeval jb P := by
      rw [he_def, haevr, haevs, map_div₀]
      field_simp

    have hunitR : ∀ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) ≠ 0 →
        Polynomial.aeval jb P ∈ R.integers ∧ (Polynomial.aeval jb P)⁻¹ ∈ R.integers := by
      intro P hP
      have hmem : coeffMap A.subtype (P.eval₂ (HahnSeries.C : ↥A →+* LaurentSeries ↥A) (jqModC ↥A)) ∈ K0 := by
        rw [← hPserK]; exact (Polynomial.aeval jb P).2
      obtain ⟨h0, hres⟩ := hRpin _ hmem
      have heq : Polynomial.aeval jb P = ⟨_, hmem⟩ := Subtype.ext (hPserK P)
      have hres_ne : R.residue ⟨⟨_, hmem⟩, h0⟩ ≠ 0 := by
        intro h
        apply hPres P hP
        rw [← hres, h]
        rfl
      have hunit : IsUnit (⟨⟨_, hmem⟩, h0⟩ : ↥R.integers) := R.isUnit_of_residue_ne_zero hres_ne
      obtain ⟨-, hzinv⟩ := (ModularCurve.KSharpPin.isUnit_iff_inv_mem _ _).mp hunit
      rw [heq]
      exact ⟨h0, hzinv⟩
    constructor
    · intro heV

      have hrelF : ModularCurve.KSharpPin.iotaSharp q M' e * Polynomial.aeval J' Q =
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (cr / cs) * Polynomial.aeval J' P := by
        rw [← hιaeval, ← hιaeval, ← hιalg, ← map_mul, ← map_mul, hrel]
      have hc : cr / cs ∈ A := by
        refine (ModularCurve.KSharpPin.mem_iff_const_mem_of_rel A (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) V hVc
          _ _ _ ?_ ?_ (hVgen P hP).1 (hVgen P hP).2 (hVgen Q hQ).1 (hVgen Q hQ).2 hrelF).mp heV
        · rw [← hιaeval]; exact fun h => hPne ((ModularCurve.KSharpPin.iotaSharp q M').injective (by rw [h, map_zero]))
        · rw [← hιaeval]; exact fun h => hQne ((ModularCurve.KSharpPin.iotaSharp q M').injective (by rw [h, map_zero]))
      exact (ModularCurve.KSharpPin.mem_iff_const_mem_of_rel A (algebraMap (AlgebraicClosure ℚ) ↥K0) R.integers
        R.algebraMap_mem_iff _ _ _ hPne hQne (hunitR P hP).1 (hunitR P hP).2 (hunitR Q hQ).1 (hunitR Q hQ).2 hrel).mpr hc
    · intro heR
      have hc : cr / cs ∈ A :=
        (ModularCurve.KSharpPin.mem_iff_const_mem_of_rel A (algebraMap (AlgebraicClosure ℚ) ↥K0) R.integers
          R.algebraMap_mem_iff _ _ _ hPne hQne (hunitR P hP).1 (hunitR P hP).2 (hunitR Q hQ).1 (hunitR Q hQ).2 hrel).mp heR
      have hrelF : ModularCurve.KSharpPin.iotaSharp q M' e * Polynomial.aeval J' Q =
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (cr / cs) * Polynomial.aeval J' P := by
        rw [← hιaeval, ← hιaeval, ← hιalg, ← map_mul, ← map_mul, hrel]
      refine (ModularCurve.KSharpPin.mem_iff_const_mem_of_rel A (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) V hVc
        _ _ _ ?_ ?_ (hVgen P hP).1 (hVgen P hP).2 (hVgen Q hQ).1 (hVgen Q hQ).2 hrelF).mpr hc
      · rw [← hιaeval]; exact fun h => hPne ((ModularCurve.KSharpPin.iotaSharp q M').injective (by rw [h, map_zero]))
      · rw [← hιaeval]; exact fun h => hQne ((ModularCurve.KSharpPin.iotaSharp q M').injective (by rw [h, map_zero]))

  have hVO : O.comap (ModularCurve.KSharpPin.iotaSharp q M') = R.integers :=
    AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨jb, hjbO⟩ hjresT hfin hdeg _
      (hV_of O hOA hgenO')
  have hVI : (OIg (lineInfty q)).comap (ModularCurve.KSharpPin.iotaSharp q M') = R.integers :=
    AlgebraicCurve.RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨jb, hjbO⟩ hjresT hfin hdeg _
      (hV_of (OIg (lineInfty q)) hconstI hgenI')

  have hxι : x = ModularCurve.KSharpPin.iotaSharp q M' ⟨g, hg⟩ := Subtype.ext hx
  rw [hxι, ← ValuationSubring.mem_comap, ← ValuationSubring.mem_comap, hVO, hVI]

end S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem (solution)
