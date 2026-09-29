-- Prove2me | solution 1 for ModularCurve.vcXInv_velu2X_and_vcYInv_velu2Y_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/5b8eae92-a8d4-59a2-a510-8ecbdcd7a363

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero
import Theorems.Thm_ModularCurve_toricPoint_fst_coeff_mul
import Theorems.Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd
import Theorems.Thm_ModularCurve_toricPoint_fst_coeff_zero
import Theorems.Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors
import Theorems.Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd
import Theorems.Thm_ModularCurve_toricPoint_snd_coeff_zero
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_vcXInv_velu2X_and_vcYInv_velu2Y_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_sq
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u

namespace Step2Pts

section Velu

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem addX_eq_of_veluGy_eq_zero {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) = x₀ + W.veluGx x₀ y₀ / (x - x₀) := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.equation_iff] at hP hQ
  simp only [veluGy] at hgy
  have hcl : (y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀ + x₀) * (x - x₀) ^ 2
      - W.veluGx x₀ y₀ * (x - x₀) = 0 := by
    simp only [veluGx]
    linear_combination hP - hQ + (y - y₀) * hgy
  have hid : W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) - (x₀ + W.veluGx x₀ y₀ / (x - x₀)) =
      ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀ + x₀) * (x - x₀) ^ 2
        - W.veluGx x₀ y₀ * (x - x₀)) / (x - x₀) ^ 2 := by
    rw [Affine.slope_of_X_ne hx]
    simp only [Affine.addX]
    field_simp
    ring
  rw [← sub_eq_zero, hid, hcl, zero_div]

theorem addY_eq_of_veluGy_eq_zero {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) =
      y₀ - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2 := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have hX := addX_eq_of_veluGy_eq_zero W hP hQ hgy hx
  simp only [Affine.addY, Affine.negAddY, Affine.negY]
  rw [hX, Affine.slope_of_X_ne hx]
  simp only [veluGy] at hgy
  calc _ = y₀ - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2
        + -(2 * y₀ + W.a₁ * x₀ + W.a₃) := by
          field_simp
          ring
    _ = _ := by rw [hgy, add_zero]

theorem velu2X_eq_add {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.velu2X x₀ y₀ x = x + W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) - x₀ := by
  rw [addX_eq_of_veluGy_eq_zero W hP hQ hgy hx, velu2X]
  ring

theorem velu2Y_eq_add {x₀ y₀ x y : F}
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hx : x ≠ x₀) :
    W.velu2Y x₀ y₀ x y = y + W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) - y₀ := by
  rw [addY_eq_of_veluGy_eq_zero W hP hQ hgy hx, velu2Y]
  ring

end Velu

section LevelOne

variable (K : Type u) [Field K] [CharZero K]

theorem toricPoint_fst_ne (c : K) (hcm1 : c ≠ -1) (hc1 : c ≠ 1) :
    (toricPoint K 1 c).1 ≠ (toricPoint K 1 (-1)).1 := by
  intro h
  have h0 := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  simp only [toricPoint_fst_coeff_zero] at h0
  have h1c : (1 - c) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hc1))
  norm_num at h0
  rw [div_eq_iff h1c] at h0
  have hsq : (c + 1) ^ 2 = 0 := by linear_combination 4 * h0
  exact hcm1 (by linear_combination (pow_eq_zero_iff two_ne_zero).mp hsq)

theorem velu2_toricPoint_level_one (c : K) (hc0 : c ≠ 0) (hc2 : c ^ 2 ≠ 1) :
    (tateLaurent K).velu2X (toricPoint K 1 (-1)).1 (toricPoint K 1 (-1)).2 (toricPoint K 1 c).1 =
        (toricPoint K 1 c).1 + (toricPoint K 1 (-c)).1 - (toricPoint K 1 (-1)).1 ∧
      (tateLaurent K).velu2Y (toricPoint K 1 (-1)).1 (toricPoint K 1 (-1)).2 (toricPoint K 1 c).1
          (toricPoint K 1 c).2 =
        (toricPoint K 1 c).2 + (toricPoint K 1 (-c)).2 - (toricPoint K 1 (-1)).2 := by
  classical
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, one_pow])
  have hcm1 : c ≠ -1 := fun h => hc2 (by rw [h]; norm_num)
  obtain ⟨hPc, hPm, -, hadd⟩ :=
    toricPoint_add_toricPoint_of_charZero K c (-1) hc0 (by norm_num) hc1 (by norm_num)
  have hprod : c * (-1) ≠ 1 := by
    rw [mul_neg_one]
    intro h
    exact hcm1 (by rw [← h, neg_neg])
  obtain ⟨hPmc, hsum⟩ := hadd hprod

  obtain ⟨hPm', hPm'', htwo, -⟩ :=
    toricPoint_add_toricPoint_of_charZero K (-1 : K) (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := htwo (by norm_num)
  rw [add_eq_zero_iff_eq_neg, Affine.Point.neg_some] at h2
  have hneg := (Affine.Point.some.inj h2).2
  have hgy : (tateLaurent K).veluGy (toricPoint K 1 (-1)).1 (toricPoint K 1 (-1)).2 = 0 :=
    (tateLaurent K).veluGy_eq_zero_of_negY_eq hneg.symm
  have hx := toricPoint_fst_ne K c hcm1 hc1
  rw [Affine.Point.add_of_X_ne hx] at hsum
  obtain ⟨hX, hY⟩ := Affine.Point.some.inj hsum
  rw [mul_neg_one] at hX hY
  refine ⟨?_, ?_⟩
  · rw [velu2X_eq_add _ hPc.1 hPm.1 hgy hx, hX]
  · rw [velu2Y_eq_add _ hPc.1 hPm.1 hgy hx, hY]

end LevelOne

section Series

variable (K : Type u) [Field K] [CharZero K]

theorem ofPowerSeries_coeff_neg (f : PowerSeries K) (n : ℕ) (hn : 0 < n) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff (-(n : ℤ)) = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨k, hk⟩
  change (k : ℤ) = -(n : ℤ) at hk
  omega

theorem toricPoint_coeff_neg (p : ℕ) (c : K) (n : ℕ) (hn : 0 < n) :
    (toricPoint K p c).1.coeff (-(n : ℤ)) = 0 ∧ (toricPoint K p c).2.coeff (-(n : ℤ)) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [toricPoint_fst]; exact ofPowerSeries_coeff_neg K _ n hn
  · rw [toricPoint_snd]; exact ofPowerSeries_coeff_neg K _ n hn

theorem coeff_C' (a : K) (n : ℤ) : (HahnSeries.C a : LaurentSeries K).coeff n = if n = 0 then a else 0 := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem coeff_ofNat_mul (k : ℕ) [k.AtLeastTwo] (s : LaurentSeries K) (n : ℤ) :
    ((no_index (OfNat.ofNat k) : LaurentSeries K) * s).coeff n = (OfNat.ofNat k : K) * s.coeff n := by
  rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := K)) k, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    smul_eq_mul]

theorem X1_coeff (c : K) {m : ℕ} (hm : m ≠ 0) :
    (toricPoint K 1 c).1.coeff (m : ℤ) = ∑ e ∈ m.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2) := by
  have h := toricPoint_fst_coeff_mul K 1 one_pos c hm
  rwa [one_mul] at h

theorem Y1_coeff (c : K) {m : ℕ} (hm : m ≠ 0) :
    (toricPoint K 1 c).2.coeff (m : ℤ) =
      ∑ e ∈ m.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) := by
  have h := toricPoint_snd_coeff_mul_eq_sum_divisors K 1 one_pos c hm
  rwa [one_mul] at h

theorem sum_divisors_two_mul (M : ℕ) (hM : M ≠ 0) (f g : ℕ → K)
    (hodd : ∀ e, Odd e → f e = 0) (heven : ∀ e, f (2 * e) = g e) :
    ∑ e ∈ (2 * M).divisors, f e = ∑ e ∈ M.divisors, g e := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (2 * M).divisors (fun e => Even e)]
  have hz : ∑ e ∈ (2 * M).divisors with ¬ Even e, f e = 0 :=
    Finset.sum_eq_zero fun e he => hodd e (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp he).2)
  rw [hz, add_zero]
  have himg : (2 * M).divisors.filter (fun e => Even e) = M.divisors.image (fun e => 2 * e) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, hM⟩, by ring⟩
      have hd' : 2 * k ∣ 2 * M := by rwa [two_mul]
      exact Nat.dvd_of_mul_dvd_mul_left two_pos hd'
    · rintro ⟨k, ⟨hk, -⟩, rfl⟩
      exact ⟨⟨mul_dvd_mul_left 2 hk, by omega⟩, even_two_mul k⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => by omega)]
  exact Finset.sum_congr rfl fun e _ => heven e

theorem sum_divisors_odd (m : ℕ) (hm : ¬ 2 ∣ m) (f : ℕ → K) (hodd : ∀ e, Odd e → f e = 0) :
    ∑ e ∈ m.divisors, f e = 0 := by
  have hmo : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)
  exact Finset.sum_eq_zero fun e he => hodd e (hmo.of_dvd_nat (Nat.dvd_of_mem_divisors he))

theorem const_X (c : K) (h1c : 1 - c ≠ 0) (h1c' : 1 + c ≠ 0) :
    c / (1 - c) ^ 2 + -c / (1 + c) ^ 2 - -1 / (1 + 1 : K) ^ 2 =
      4 * (c ^ 2 / ((1 - c) * (1 + c)) ^ 2) + 1 / 4 := by
  field_simp
  ring

theorem const_Y (c : K) (h1c : 1 - c ≠ 0) (h1c' : 1 + c ≠ 0) :
    c ^ 2 / (1 - c) ^ 3 + (-c) ^ 2 / (1 + c) ^ 3 - (-1) ^ 2 / (1 + 1 : K) ^ 3 =
      8 * ((c ^ 2) ^ 2 / ((1 - c) * (1 + c)) ^ 3) + 2 * (c ^ 2 / ((1 - c) * (1 + c)) ^ 2) - 1 / 8 := by
  field_simp
  ring

theorem X_dup (c : K) (hc0 : c ≠ 0) (hc2 : c ^ 2 ≠ 1) :
    (toricPoint K 1 c).1 + (toricPoint K 1 (-c)).1 - (toricPoint K 1 (-1)).1 =
      4 * (toricPoint K 2 (c ^ 2)).1 + HahnSeries.C (1 / 4 : K) := by
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, one_pow])
  have hcm1 : c ≠ -1 := fun h => hc2 (by rw [h]; norm_num)
  have h1c : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have h1c' : (1 + c) ≠ 0 := by
    intro h; exact hcm1 (by linear_combination h)
  have h1c2 : (1 - c ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc2)

  set f : ℕ → K := fun e =>
    (e : K) * (c ^ e + c⁻¹ ^ e - 2) + (e : K) * ((-c) ^ e + (-c)⁻¹ ^ e - 2)
      - (e : K) * ((-1) ^ e + (-1 : K)⁻¹ ^ e - 2) with hf
  set g : ℕ → K := fun e => 4 * ((e : K) * ((c ^ 2) ^ e + (c ^ 2)⁻¹ ^ e - 2)) with hg
  have hodd : ∀ e, Odd e → f e = 0 := by
    intro e he
    simp only [hf, inv_neg, he.neg_pow, inv_one, one_pow]
    ring
  have heven : ∀ e, f (2 * e) = g e := by
    intro e
    have h2e : Even (2 * e) := even_two_mul e
    simp only [hf, hg, inv_neg, h2e.neg_pow, inv_one, one_pow]
    push_cast
    ring
  have hnat : ∀ m : ℕ,
      ((toricPoint K 1 c).1 + (toricPoint K 1 (-c)).1 - (toricPoint K 1 (-1)).1).coeff (m : ℤ) =
        (4 * (toricPoint K 2 (c ^ 2)).1 + HahnSeries.C (1 / 4 : K)).coeff (m : ℤ) := by
    intro m
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_ofNat_mul, coeff_C']
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, toricPoint_fst_coeff_zero, if_true]
      linear_combination const_X K c h1c h1c'
    · have hm0 : m ≠ 0 := hm.ne'
      rw [if_neg (by exact_mod_cast hm0), X1_coeff K c hm0, X1_coeff K (-c) hm0, X1_coeff K (-1) hm0,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, add_zero]
      by_cases h2 : 2 ∣ m
      · obtain ⟨M, rfl⟩ := h2
        have hM : M ≠ 0 := by rintro rfl; exact hm0 rfl
        rw [toricPoint_fst_coeff_mul K 2 two_pos (c ^ 2) hM, Finset.mul_sum]
        exact sum_divisors_two_mul K M hM f g hodd heven
      · rw [toricPoint_fst_coeff_of_not_dvd K 2 (c ^ 2) h2, mul_zero]
        exact sum_divisors_odd K m h2 f hodd
  ext n
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact hnat m
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hnat 0
    · simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_ofNat_mul, coeff_C',
        (toricPoint_coeff_neg K _ _ m hm).1, if_neg (show (-(m : ℤ)) ≠ 0 by omega)]
      ring

theorem Y_dup (c : K) (hc0 : c ≠ 0) (hc2 : c ^ 2 ≠ 1) :
    (toricPoint K 1 c).2 + (toricPoint K 1 (-c)).2 - (toricPoint K 1 (-1)).2 =
      8 * (toricPoint K 2 (c ^ 2)).2 + 2 * (toricPoint K 2 (c ^ 2)).1 - HahnSeries.C (1 / 8 : K) := by
  have hc1 : c ≠ 1 := fun h => hc2 (by rw [h, one_pow])
  have hcm1 : c ≠ -1 := fun h => hc2 (by rw [h]; norm_num)
  have h1c : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have h1c' : (1 + c) ≠ 0 := by
    intro h; exact hcm1 (by linear_combination h)
  have h1c2 : (1 - c ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc2)
  have hch : ∀ a : ℕ, ((a.choose 2 : ℕ) : K) = a * (a - 1) / 2 := fun a => Nat.cast_choose_two K a
  set f : ℕ → K := fun e =>
    (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K))
      + (((e.choose 2 : ℕ) : K) * ((-c) ^ e - (-c)⁻¹ ^ e) - (e : K) * (-c)⁻¹ ^ e + (e : K))
      - (((e.choose 2 : ℕ) : K) * ((-1) ^ e - (-1 : K)⁻¹ ^ e) - (e : K) * (-1 : K)⁻¹ ^ e + (e : K)) with hf
  set g : ℕ → K := fun e =>
    8 * (((e.choose 2 : ℕ) : K) * ((c ^ 2) ^ e - (c ^ 2)⁻¹ ^ e) - (e : K) * (c ^ 2)⁻¹ ^ e + (e : K))
      + 2 * ((e : K) * ((c ^ 2) ^ e + (c ^ 2)⁻¹ ^ e - 2)) with hg
  have hodd : ∀ e, Odd e → f e = 0 := by
    intro e he
    simp only [hf, inv_neg, he.neg_pow, inv_one, one_pow, he.neg_one_pow]
    ring
  have heven : ∀ e, f (2 * e) = g e := by
    intro e
    have h2e : Even (2 * e) := even_two_mul e
    simp only [hf, hg, inv_neg, h2e.neg_pow, inv_one, one_pow, h2e.neg_one_pow, hch]
    push_cast
    field_simp
    ring
  have hnat : ∀ m : ℕ,
      ((toricPoint K 1 c).2 + (toricPoint K 1 (-c)).2 - (toricPoint K 1 (-1)).2).coeff (m : ℤ) =
        (8 * (toricPoint K 2 (c ^ 2)).2 + 2 * (toricPoint K 2 (c ^ 2)).1
          - HahnSeries.C (1 / 8 : K)).coeff (m : ℤ) := by
    intro m
    simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_ofNat_mul, coeff_C']
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, toricPoint_fst_coeff_zero, toricPoint_snd_coeff_zero, if_true]
      linear_combination const_Y K c h1c h1c'
    · have hm0 : m ≠ 0 := hm.ne'
      rw [if_neg (by exact_mod_cast hm0), Y1_coeff K c hm0, Y1_coeff K (-c) hm0, Y1_coeff K (-1) hm0,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, sub_zero]
      by_cases h2 : 2 ∣ m
      · obtain ⟨M, rfl⟩ := h2
        have hM : M ≠ 0 := by rintro rfl; exact hm0 rfl
        rw [toricPoint_snd_coeff_mul_eq_sum_divisors K 2 two_pos (c ^ 2) hM,
          toricPoint_fst_coeff_mul K 2 two_pos (c ^ 2) hM, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact sum_divisors_two_mul K M hM f g hodd heven
      · rw [toricPoint_snd_coeff_of_not_dvd K 2 (c ^ 2) h2, toricPoint_fst_coeff_of_not_dvd K 2 (c ^ 2) h2,
          mul_zero, mul_zero, add_zero]
        exact sum_divisors_odd K m h2 f hodd
  ext n
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact hnat m
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using hnat 0
    · simp only [HahnSeries.coeff_add, HahnSeries.coeff_sub, coeff_ofNat_mul, coeff_C',
        (toricPoint_coeff_neg K _ _ m hm).1, (toricPoint_coeff_neg K _ _ m hm).2,
        if_neg (show (-(m : ℤ)) ≠ 0 by omega)]
      ring

end Series

section Transport

variable {R S : Type*} [Field R] [Field S] (φ : R →+* S) (W : WeierstrassCurve R)

theorem map_velu2X (x₀ y₀ x : R) :
    (W.map φ).velu2X (φ x₀) (φ y₀) (φ x) = φ (W.velu2X x₀ y₀ x) := by
  simp only [velu2X, veluGx, map_a₁, map_a₂, map_a₄, map_add, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat]

theorem map_velu2Y (x₀ y₀ x y : R) :
    (W.map φ).velu2Y (φ x₀) (φ y₀) (φ x) (φ y) = φ (W.velu2Y x₀ y₀ x y) := by
  simp only [velu2Y, veluGx, map_a₁, map_a₂, map_a₄, map_add, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat]

end Transport

end Step2Pts

open Step2Pts in
theorem solution
    (K : Type u) [Field K] [CharZero K] (m : ℕ) [NeZero m]
    (C : WeierstrassCurve.VariableChange (LaurentSeries K))
    (hu : (C.u : LaurentSeries K) = (2 : LaurentSeries K))
    (hr : C.r = HahnSeries.C ((1 : K) / 4))
    (hs : C.s = HahnSeries.C ((1 : K) / 2))
    (ht : C.t = HahnSeries.C (-((1 : K) / 8)))
    (c : K) (hc0 : c ≠ 0) (hc2 : c ^ 2 ≠ 1) :
    WeierstrassCurve.Affine.vcXInv C
        (((tateLaurent K).map (qExpand K m)).velu2X (toricPoint K m (-1)).1 (toricPoint K m (-1)).2 (toricPoint K m c).1) =
      (toricPoint K (m * 2) (c ^ 2)).1 ∧
    WeierstrassCurve.Affine.vcYInv C
        (((tateLaurent K).map (qExpand K m)).velu2X (toricPoint K m (-1)).1 (toricPoint K m (-1)).2 (toricPoint K m c).1)
        (((tateLaurent K).map (qExpand K m)).velu2Y (toricPoint K m (-1)).1 (toricPoint K m (-1)).2
          (toricPoint K m c).1 (toricPoint K m c).2) =
      (toricPoint K (m * 2) (c ^ 2)).2 := by
  haveI : CharZero (LaurentSeries K) :=
    charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective
  have hlev : ∀ a : K, toricPoint K m a =
      (qExpand K m (toricPoint K 1 a).1, qExpand K m (toricPoint K 1 a).2) := fun a => by
    have h := toricPoint_level_mul K 1 m a
    rwa [mul_one] at h
  have hlev2 := toricPoint_level_mul K 2 m (c ^ 2)
  obtain ⟨hX1, hY1⟩ := velu2_toricPoint_level_one K c hc0 hc2
  have hXd := X_dup K c hc0 hc2
  have hYd := Y_dup K c hc0 hc2
  rw [hlev c, hlev (-1), hlev2]
  dsimp only
  rw [map_velu2X, map_velu2Y, hX1, hY1, hXd, hYd]
  simp only [Affine.vcXInv, Affine.vcYInv, Units.val_inv_eq_inv_val, hu, hr, hs, ht, map_add, map_sub,
    map_mul, map_ofNat, qExpand_C, map_div₀, map_one, map_neg]
  constructor
  · field_simp
    ring
  · field_simp
    ring

end S_ModularCurve_vcXInv_velu2X_and_vcYInv_velu2Y_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_sq
end P2MW
export P2MW.S_ModularCurve_vcXInv_velu2X_and_vcYInv_velu2Y_toricPoint_tateLaurent_map_qExpand_eq_toricPoint_sq (solution)
