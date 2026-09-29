-- Prove2me | solution 1 for ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/57098483-8346-54d6-bb69-7960a817b396

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve
p2m_export "ModularCurve" "tateBase toricPoint tateLaurent qExpand qExpand_injective toricPoint_add_toricPoint_of_charZero toricPoint_level_mul"
namespace P2MToricAddBase
p2m_open "ModularCurve"

universe u v

section Transport

variable {R : Type u} {S : Type v} [Field R] [Field S] [DecidableEq R] [DecidableEq S]
variable (W : WeierstrassCurve R) (φ : R →+* S)

def mapPt : W.toAffine.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) ((Affine.map_nonsingular W φ.injective x y).mpr h)

@[scoped simp] theorem mapPt_zero : mapPt W φ (0 : W.toAffine.Point) = 0 := rfl

theorem mapPt_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapPt W φ (.some x y h) =
      .some (φ x) (φ y) ((Affine.map_nonsingular W φ.injective x y).mpr h) := rfl

theorem point_some_congr {T : Type*} [CommRing T] {V : WeierstrassCurve T} {x x' y y' : T}
    (hx : x = x') (hy : y = y') (h : V.toAffine.Nonsingular x y) (h' : V.toAffine.Nonsingular x' y') :
    (Point.some x y h : V.toAffine.Point) = Point.some x' y' h' := by
  subst hx; subst hy; rfl

theorem mapPt_add (P Q : W.toAffine.Point) :
    mapPt W φ (P + Q) = mapPt W φ P + mapPt W φ Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, mapPt_zero, mapPt_some, mapPt_some,
        Point.add_of_Y_eq (congrArg φ hxy.1) (by rw [hxy.2, Affine.map_negY])]
    · have hxy' : ¬ (φ x₁ = φ x₂ ∧ φ y₁ = (W.map φ).toAffine.negY (φ x₂) (φ y₂)) := by
        rintro ⟨hx, hy⟩
        exact hxy ⟨φ.injective hx, φ.injective (by rwa [Affine.map_negY] at hy)⟩
      rw [Point.add_some hxy, mapPt_some, mapPt_some, mapPt_some, Point.add_some hxy']
      refine point_some_congr ?_ ?_ _ _
      · rw [Affine.map_slope, Affine.map_addX]
      · rw [Affine.map_slope, Affine.map_addY]

end Transport

section Base

variable (F : Type u) [Field F] (M : ℕ) [NeZero M]

theorem tateBase_eq_map : tateBase F M = (tateLaurent F).map (qExpand F M) := rfl

theorem toricPoint_eq_qExpand (c : F) :
    toricPoint F M c =
      (qExpand F M (toricPoint F 1 c).1, qExpand F M (toricPoint F 1 c).2) := by
  have h := ModularCurve.toricPoint_level_mul F 1 M c
  rwa [mul_one] at h

theorem toricPoint_fst_eq (c : F) : (toricPoint F M c).1 = qExpand F M (toricPoint F 1 c).1 := by
  rw [toricPoint_eq_qExpand]

theorem toricPoint_snd_eq (c : F) : (toricPoint F M c).2 = qExpand F M (toricPoint F 1 c).2 := by
  rw [toricPoint_eq_qExpand]

end Base

theorem main (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)] (M : ℕ) [NeZero M]
    (c d : F) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hc1 : c ≠ 1) (hd1 : d ≠ 1) :
    ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M c).1 (toricPoint F M c).2)
      (hd : (tateBase F M).toAffine.Nonsingular (toricPoint F M d).1 (toricPoint F M d).2),
      (c * d = 1 →
        (Point.some (toricPoint F M c).1 (toricPoint F M c).2 hc : (tateBase F M).toAffine.Point)
          + Point.some (toricPoint F M d).1 (toricPoint F M d).2 hd = 0) ∧
      (c * d ≠ 1 →
        ∃ hcd : (tateBase F M).toAffine.Nonsingular
            (toricPoint F M (c * d)).1 (toricPoint F M (c * d)).2,
          (Point.some (toricPoint F M c).1 (toricPoint F M c).2 hc : (tateBase F M).toAffine.Point)
            + Point.some (toricPoint F M d).1 (toricPoint F M d).2 hd
            = Point.some (toricPoint F M (c * d)).1 (toricPoint F M (c * d)).2 hcd) := by
  obtain ⟨hc, hd, hinv, hmul⟩ :=
    ModularCurve.toricPoint_add_toricPoint_of_charZero F c d hc0 hd0 hc1 hd1
  set φ : LaurentSeries F →+* LaurentSeries F := qExpand F M with hφ
  have hφinj : Function.Injective φ := qExpand_injective M

  have hns : ∀ {x y : LaurentSeries F}, (tateLaurent F).toAffine.Nonsingular x y →
      (tateBase F M).toAffine.Nonsingular (φ x) (φ y) := fun h =>
    (Affine.map_nonsingular (tateLaurent F) hφinj _ _).mpr h
  have hcB : (tateBase F M).toAffine.Nonsingular (toricPoint F M c).1 (toricPoint F M c).2 := by
    rw [toricPoint_fst_eq, toricPoint_snd_eq]; exact hns hc
  have hdB : (tateBase F M).toAffine.Nonsingular (toricPoint F M d).1 (toricPoint F M d).2 := by
    rw [toricPoint_fst_eq, toricPoint_snd_eq]; exact hns hd

  have hPc : mapPt (tateLaurent F) φ (Point.some _ _ hc) =
      (Point.some (toricPoint F M c).1 (toricPoint F M c).2 hcB : (tateBase F M).toAffine.Point) := by
    rw [mapPt_some]
    exact point_some_congr (toricPoint_fst_eq F M c).symm (toricPoint_snd_eq F M c).symm _ _
  have hPd : mapPt (tateLaurent F) φ (Point.some _ _ hd) =
      (Point.some (toricPoint F M d).1 (toricPoint F M d).2 hdB : (tateBase F M).toAffine.Point) := by
    rw [mapPt_some]
    exact point_some_congr (toricPoint_fst_eq F M d).symm (toricPoint_snd_eq F M d).symm _ _
  refine ⟨hcB, hdB, fun hcd => ?_, fun hcd => ?_⟩
  · have h := congrArg (mapPt (tateLaurent F) φ) (hinv hcd)
    rw [mapPt_add, hPc, hPd, mapPt_zero] at h
    exact h
  · obtain ⟨hcd', h⟩ := hmul hcd
    have hcdB : (tateBase F M).toAffine.Nonsingular
        (toricPoint F M (c * d)).1 (toricPoint F M (c * d)).2 := by
      rw [toricPoint_fst_eq, toricPoint_snd_eq]; exact hns hcd'
    refine ⟨hcdB, ?_⟩
    have h' := congrArg (mapPt (tateLaurent F) φ) h
    rw [mapPt_add, hPc, hPd, mapPt_some] at h'
    exact h'.trans (point_some_congr (toricPoint_fst_eq F M (c * d)).symm
      (toricPoint_snd_eq F M (c * d)).symm _ _)

end ModularCurve.P2MToricAddBase
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero.ModularCurve P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero.ModularCurve.P2MToricAddBase"
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero.ModularCurve P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero.ModularCurve.P2MToricAddBase"

p2m_open "ModularCurve P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero.ModularCurve WeierstrassCurve WeierstrassCurve.Affine"

universe u in
theorem solution
    (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)] (M : ℕ) [NeZero M]
    (c d : F) (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hc1 : c ≠ 1) (hd1 : d ≠ 1) :
    ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M c).1 (toricPoint F M c).2)
      (hd : (tateBase F M).toAffine.Nonsingular (toricPoint F M d).1 (toricPoint F M d).2),
      (c * d = 1 →
        (Point.some (toricPoint F M c).1 (toricPoint F M c).2 hc : (tateBase F M).toAffine.Point)
          + Point.some (toricPoint F M d).1 (toricPoint F M d).2 hd = 0) ∧
      (c * d ≠ 1 →
        ∃ hcd : (tateBase F M).toAffine.Nonsingular
            (toricPoint F M (c * d)).1 (toricPoint F M (c * d)).2,
          (Point.some (toricPoint F M c).1 (toricPoint F M c).2 hc : (tateBase F M).toAffine.Point)
            + Point.some (toricPoint F M d).1 (toricPoint F M d).2 hd
            = Point.some (toricPoint F M (c * d)).1 (toricPoint F M (c * d)).2 hcd) :=
  ModularCurve.P2MToricAddBase.main F M c d hc0 hd0 hc1 hd1

end S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
end P2MW
export P2MW.S_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero (solution)
