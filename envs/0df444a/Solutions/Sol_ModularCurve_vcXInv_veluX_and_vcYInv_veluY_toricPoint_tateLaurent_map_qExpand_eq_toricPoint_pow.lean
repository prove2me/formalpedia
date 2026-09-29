-- Prove2me | solution 1 for ModularCurve.vcXInv_veluX_and_vcYInv_veluY_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/549549fd-633c-5663-86d8-2053deeade98

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
import Theorems.Thm_ModularCurve_sum_range_toricPoint_fst_sub_sum_Ico_eq_mul_toricPoint_pow_fst_add_C
import Theorems.Thm_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_vcXInv_veluX_and_vcYInv_veluY_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u

namespace StepPts

section MapLemmas

variable {F L : Type*} [Field F] [Field L] (φ : F →+* L) (W : WeierstrassCurve F)

theorem map_veluT (x y : F) : (W.map φ).veluT (φ x) (φ y) = φ (W.veluT x y) := by
  simp only [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, map_sub, map_mul, map_add, map_neg, map_pow, map_ofNat]

theorem map_veluU (x y : F) : (W.map φ).veluU (φ x) (φ y) = φ (W.veluU x y) := by
  simp only [WeierstrassCurve.veluU, WeierstrassCurve.veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_mul, map_add, map_neg, map_pow, map_ofNat]

theorem map_veluGx (x y : F) : (W.map φ).veluGx (φ x) (φ y) = φ (W.veluGx x y) := by
  simp only [WeierstrassCurve.veluGx, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, map_sub, map_mul, map_add, map_pow, map_ofNat]

theorem map_veluGy (x y : F) : (W.map φ).veluGy (φ x) (φ y) = φ (W.veluGy x y) := by
  simp only [WeierstrassCurve.veluGy, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    map_mul, map_add, map_neg, map_ofNat]

theorem map_veluX [DecidableEq (F × F)] [DecidableEq (L × L)] (S : Finset (F × F)) (x : F) :
    (W.map φ).veluX (S.image (Prod.map φ φ)) (φ x) = φ (W.veluX S x) := by
  unfold WeierstrassCurve.veluX
  rw [Finset.sum_image fun a _ b _ h => (Prod.map_injective.mpr ⟨φ.injective, φ.injective⟩) h,
    map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q _ => ?_)
  simp only [Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_add, map_div₀, map_sub, map_pow]

theorem map_veluY [DecidableEq (F × F)] [DecidableEq (L × L)] (S : Finset (F × F)) (x y : F) :
    (W.map φ).veluY (S.image (Prod.map φ φ)) (φ x) (φ y) = φ (W.veluY S x y) := by
  unfold WeierstrassCurve.veluY
  rw [Finset.sum_image fun a _ b _ h => (Prod.map_injective.mpr ⟨φ.injective, φ.injective⟩) h,
    map_sub, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun Q _ => ?_)
  simp only [Prod.map_fst, Prod.map_snd, map_veluT, map_veluU, map_veluGx, map_veluGy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_add, map_div₀, map_sub, map_pow, map_mul,
    map_ofNat]

theorem map_vcXInv (C : VariableChange F) (x : F) :
    Affine.vcXInv (C.map φ) (φ x) = φ (Affine.vcXInv C x) := by
  simp only [Affine.vcXInv, VariableChange.map_u, VariableChange.map_r, map_mul, map_sub, map_pow,
    Units.coe_map_inv, MonoidHom.coe_coe]

theorem map_vcYInv (C : VariableChange F) (x y : F) :
    Affine.vcYInv (C.map φ) (φ x) (φ y) = φ (Affine.vcYInv C x y) := by
  simp only [Affine.vcYInv, VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
    VariableChange.map_t, map_mul, map_sub, map_pow, Units.coe_map_inv, MonoidHom.coe_coe]

end MapLemmas

variable (K : Type u) [Field K]

theorem map_qExpand_eq_self_of_const (a : ℕ) [NeZero a] (C : VariableChange (LaurentSeries K))
    (n : ℕ) (r s t : K) (hu : (C.u : LaurentSeries K) = (n : LaurentSeries K))
    (hr : C.r = HahnSeries.C r) (hs : C.s = HahnSeries.C s) (ht : C.t = HahnSeries.C t) :
    C.map (qExpand K a) = C := by
  ext
  · rw [VariableChange.map_u, Units.coe_map, MonoidHom.coe_coe, hu, map_natCast]
  · rw [VariableChange.map_r, hr, qExpand_C]
  · rw [VariableChange.map_s, hs, qExpand_C]
  · rw [VariableChange.map_t, ht, qExpand_C]

theorem image_toricPoint_one (a : ℕ) [NeZero a] (ℓ : ℕ) (ζ : K)
    [DecidableEq (LaurentSeries K × LaurentSeries K)] :
    (((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k)).image
        (Prod.map (qExpand K a) (qExpand K a))) =
      (Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K a (ζ ^ k) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  have h := toricPoint_level_mul K 1 a (ζ ^ k)
  rw [mul_one] at h
  rw [h]
  rfl

theorem natCast_laurent_eq_C (n : ℕ) : ((n : ℕ) : LaurentSeries K) = HahnSeries.C (n : K) :=
  (map_natCast (HahnSeries.C : K →+* LaurentSeries K) n).symm

end StepPts

open StepPts in
open scoped Classical in
theorem solution
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (m : ℕ) [NeZero m]
    (C : WeierstrassCurve.VariableChange (LaurentSeries K))
    (hu : (C.u : LaurentSeries K) = (ℓ : LaurentSeries K))
    (hr : C.r = HahnSeries.C (((ℓ : K) ^ 2 - 1) / 12))
    (hs : C.s = HahnSeries.C (((ℓ : K) - 1) / 2))
    (ht : C.t = HahnSeries.C (-(((ℓ : K) ^ 2 - 1) / 24)))
    (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    WeierstrassCurve.Affine.vcXInv C
        (((tateLaurent K).map (qExpand K m)).veluX ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k))
          (toricPoint K m c).1) =
      (toricPoint K (m * ℓ) (c ^ ℓ)).1 ∧
    WeierstrassCurve.Affine.vcYInv C
        (((tateLaurent K).map (qExpand K m)).veluX ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k))
          (toricPoint K m c).1)
        (((tateLaurent K).map (qExpand K m)).veluY ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k))
          (toricPoint K m c).1 (toricPoint K m c).2) =
      (toricPoint K (m * ℓ) (c ^ ℓ)).2 := by
  have hℓ : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  set X1 : LaurentSeries K := (toricPoint K 1 c).1 with hX1
  set Y1 : LaurentSeries K := (toricPoint K 1 c).2 with hY1
  set S1 : Finset (LaurentSeries K × LaurentSeries K) :=
    (Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k) with hS1
  obtain ⟨hOX, hOY⟩ :=
    veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico K ℓ hℓ2 ζ hζ c hc0 hcℓ
  have hDX := sum_range_toricPoint_fst_sub_sum_Ico_eq_mul_toricPoint_pow_fst_add_C K ℓ hℓ2 ζ hζ c hc0 hcℓ
  have hDY := sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add K ℓ hℓ2 ζ hζ c hc0 hcℓ
  rw [← hS1, ← hX1] at hOX
  rw [← hS1, ← hX1, ← hY1] at hOY
  have hℓL : ((ℓ : ℕ) : LaurentSeries K) ≠ 0 := by
    rw [natCast_laurent_eq_C]; exact (map_ne_zero HahnSeries.C).mpr (Nat.cast_ne_zero.mpr hℓ.ne_zero)
  have huinv : ((C.u⁻¹ : (LaurentSeries K)ˣ) : LaurentSeries K) = ((ℓ : ℕ) : LaurentSeries K)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hu]
  have hone_x : Affine.vcXInv C ((tateLaurent K).veluX S1 X1) = (toricPoint K ℓ (c ^ ℓ)).1 := by
    rw [Affine.vcXInv, hOX, hDX, huinv, hr, add_sub_cancel_right, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hℓL, one_pow, one_mul]
  have hone_y : Affine.vcYInv C ((tateLaurent K).veluX S1 X1) ((tateLaurent K).veluY S1 X1 Y1) =
      (toricPoint K ℓ (c ^ ℓ)).2 := by
    rw [Affine.vcYInv, hOX, hOY, hDX, hDY, huinv, hr, hs, ht, add_sub_cancel_right]
    have hkey : (ℓ : LaurentSeries K) ^ 3 * (toricPoint K ℓ (c ^ ℓ)).2 +
          HahnSeries.C ((ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2) * (toricPoint K ℓ (c ^ ℓ)).1 -
          HahnSeries.C (((ℓ : K) ^ 2 - 1) / 24) - HahnSeries.C (-(((ℓ : K) ^ 2 - 1) / 24)) -
          HahnSeries.C (((ℓ : K) - 1) / 2) * ((ℓ : LaurentSeries K) ^ 2 * (toricPoint K ℓ (c ^ ℓ)).1) =
        (ℓ : LaurentSeries K) ^ 3 * (toricPoint K ℓ (c ^ ℓ)).2 := by
      have h1 : HahnSeries.C ((ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2) =
          HahnSeries.C (((ℓ : K) - 1) / 2) * (ℓ : LaurentSeries K) ^ 2 := by
        rw [natCast_laurent_eq_C, ← map_pow, ← map_mul]; congr 1; ring
      have h2 : HahnSeries.C (-(((ℓ : K) ^ 2 - 1) / 24)) = -HahnSeries.C (((ℓ : K) ^ 2 - 1) / 24) :=
        map_neg (HahnSeries.C : K →+* LaurentSeries K) _
      rw [h1, h2]; ring
    rw [hkey, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hℓL, one_pow, one_mul]

  haveI : NeZero (m * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne m) hℓ.ne_zero⟩
  have hCmap : C.map (qExpand K m) = C := map_qExpand_eq_self_of_const K m C ℓ _ _ _ hu hr hs ht
  have hPm : toricPoint K m c = (qExpand K m X1, qExpand K m Y1) := by
    have h := toricPoint_level_mul K 1 m c
    rw [mul_one] at h
    exact h
  have hPmℓ := toricPoint_level_mul K ℓ m (c ^ ℓ)
  have hSm : ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K m (ζ ^ k)) =
      S1.image (Prod.map (qExpand K m) (qExpand K m)) := (image_toricPoint_one K m ℓ ζ).symm
  rw [hPm, hPmℓ, hSm]
  simp only
  rw [map_veluX, map_veluY]
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← hCmap]
    rw [map_vcXInv, hone_x]
  · conv_lhs => rw [← hCmap]
    rw [map_vcYInv, hone_y]

end S_ModularCurve_vcXInv_veluX_and_vcYInv_veluY_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_pow
end P2MW
export P2MW.S_ModularCurve_vcXInv_veluX_and_vcYInv_veluY_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_pow (solution)
