-- Prove2me | solution 1 for ModularCurve.veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d4b2a2d5-7440-55f0-bdbe-35914b1046ee

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve WeierstrassCurve

universe u

namespace Orb

section Generic

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem pair_x_cleared (x y x₀ y₀ L₁ L₂ : F)
    (hP : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hQ : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ = x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    (hL₁ : L₁ * (x - x₀) = y - y₀) (hL₂ : L₂ * (x - x₀) = y - W.toAffine.negY x₀ y₀) :
    W.veluT x₀ y₀ * (x - x₀) ^ 2 + (x - x₀) * W.veluU x₀ y₀ =
      (W.toAffine.addX x x₀ L₁ + W.toAffine.addX x x₀ L₂ - 2 * x₀) * ((x - x₀) * (x - x₀) ^ 2) := by
  simp only [Affine.negY] at hL₂
  simp only [Affine.addX, veluT, veluU, veluGx, veluGy]
  linear_combination
    (-L₁*x^2 + 2*L₁*x*x₀ - L₁*x₀^2 - W.a₁*x^2 + 2*W.a₁*x*x₀ - W.a₁*x₀^2 - x*y + x*y₀ + x₀*y - x₀*y₀) *
      hL₁ + (-L₂*x^2 + 2*L₂*x*x₀ - L₂*x₀^2 - W.a₁*x^2 + W.a₁*x*x₀ - W.a₃*x + W.a₃*x₀ - x*y - x*y₀ +
      x₀*y + x₀*y₀) * hL₂ + (-2*x + 2*x₀) * hP + (2*x - 2*x₀) * hQ

theorem pair_y_cleared (x y x₀ y₀ L₁ L₂ : F)
    (hP : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hQ : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ = x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    (hL₁ : L₁ * (x - x₀) = y - y₀) (hL₂ : L₂ * (x - x₀) = y - W.toAffine.negY x₀ y₀) :
    -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) +
        W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀) +
        (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀)) =
      (W.toAffine.addY x x₀ y L₁ + W.toAffine.addY x x₀ y L₂ - y₀ - W.toAffine.negY x₀ y₀) *
        (x - x₀) ^ 3 := by
  simp only [Affine.negY] at hL₂
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, veluT, veluU, veluGx, veluGy]
  linear_combination
    (L₁^2*x^2 - 2*L₁^2*x*x₀ + L₁^2*x₀^2 + 2*L₁*W.a₁*x^2 - 4*L₁*W.a₁*x*x₀ + 2*L₁*W.a₁*x₀^2 + L₁*x*y -
      L₁*x*y₀ - L₁*x₀*y + L₁*x₀*y₀ + W.a₁^2*x^2 - 2*W.a₁^2*x*x₀ + W.a₁^2*x₀^2 + 2*W.a₁*x*y -
      2*W.a₁*x*y₀ - 2*W.a₁*x₀*y + 2*W.a₁*x₀*y₀ - W.a₂*x^2 + 2*W.a₂*x*x₀ - W.a₂*x₀^2 - 2*x^3 +
      3*x^2*x₀ - x₀^3 + y^2 - 2*y*y₀ + y₀^2) * hL₁ + (L₂^2*x^2 - 2*L₂^2*x*x₀ + L₂^2*x₀^2 +
      2*L₂*W.a₁*x^2 - 3*L₂*W.a₁*x*x₀ + L₂*W.a₁*x₀^2 + L₂*W.a₃*x - L₂*W.a₃*x₀ + L₂*x*y + L₂*x*y₀ -
      L₂*x₀*y - L₂*x₀*y₀ + W.a₁^2*x^2 + 2*W.a₁*W.a₃*x + 2*W.a₁*x*y + 2*W.a₁*x*y₀ - W.a₂*x^2 +
      2*W.a₂*x*x₀ - W.a₂*x₀^2 + W.a₃^2 + 2*W.a₃*y + 2*W.a₃*y₀ - 2*x^3 + 3*x^2*x₀ - x₀^3 + y^2 +
      2*y*y₀ + y₀^2) * hL₂ + (2*W.a₁*x - W.a₁*x₀ + W.a₃ + 2*y) * hP + (-2*W.a₁*x + W.a₁*x₀ - W.a₃ -
      2*y) * hQ

theorem pair_x [DecidableEq F] {x y x₀ y₀ : F} (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hx : x ≠ x₀) :
    W.veluT x₀ y₀ / (x - x₀) + W.veluU x₀ y₀ / (x - x₀) ^ 2 =
      W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y y₀) +
        W.toAffine.addX x x₀ (W.toAffine.slope x x₀ y (W.toAffine.negY x₀ y₀)) - 2 * x₀ := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  rw [Affine.equation_iff] at hP hQ
  rw [div_add_div _ _ hd (pow_ne_zero 2 hd), div_eq_iff (mul_ne_zero hd (pow_ne_zero 2 hd))]
  exact pair_x_cleared W x y x₀ y₀ _ _ hP hQ
    (by rw [Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hd])
    (by rw [Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hd])

theorem pair_y [DecidableEq F] {x y x₀ y₀ : F} (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hx : x ≠ x₀) :
    -(W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) / (x - x₀) ^ 3 +
        W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2 +
        (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (x - x₀) ^ 2) =
      W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y y₀) +
        W.toAffine.addY x x₀ y (W.toAffine.slope x x₀ y (W.toAffine.negY x₀ y₀)) - y₀ -
          W.toAffine.negY x₀ y₀ := by
  have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
  have h3 : (x - x₀) ^ 3 ≠ 0 := pow_ne_zero 3 hd
  rw [Affine.equation_iff] at hP hQ
  have hA : W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) / (x - x₀) ^ 3 +
        W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) / (x - x₀) ^ 2 +
        (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) / (x - x₀) ^ 2 =
      (W.veluU x₀ y₀ * (2 * y + W.a₁ * x + W.a₃) +
        W.veluT x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀) +
        (W.a₁ * W.veluU x₀ y₀ - W.veluGx x₀ y₀ * W.veluGy x₀ y₀) * (x - x₀)) / (x - x₀) ^ 3 := by
    have h2 : (x - x₀) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    rw [div_add_div _ _ h3 h2, div_add_div _ _ (mul_ne_zero h3 h2) h2,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero h3 h2) h2) h3]
    ring
  rw [hA, ← neg_div, div_eq_iff h3]
  exact pair_y_cleared W x y x₀ y₀ _ _ hP hQ
    (by rw [Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hd])
    (by rw [Affine.slope_of_X_ne hx, div_mul_cancel₀ _ hd])

end Generic

section Toric

variable (K : Type u) [Field K]

theorem toricPoint_fst_coeff_zero (p : ℕ) (c : K) :
    (toricPoint K p c).1.coeff (0 : ℤ) = c / (1 - c) ^ 2 := by
  rw [toricPoint_fst, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
    HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_pos rfl]

theorem toricPoint_fst_ne (p : ℕ) {c d : K} (hc1 : c ≠ 1) (hd1 : d ≠ 1) (hcd : c ≠ d)
    (hcd' : c * d ≠ 1) : (toricPoint K p c).1 ≠ (toricPoint K p d).1 := by
  intro h
  have hx := congrArg (fun f : LaurentSeries K => f.coeff (0 : ℤ)) h
  simp only [toricPoint_fst_coeff_zero] at hx
  rw [div_eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hc1)))
    (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hd1)))] at hx
  have hkey : (c - d) * (1 - c * d) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hkey with h0 | h0
  · exact hcd (sub_eq_zero.mp h0)
  · exact hcd' (by linear_combination -h0)

theorem sum_Ico_eq_sum_half_pair {M : Type*} [AddCommMonoid M] (p : ℕ) (hp : Odd p)
    (f : ℕ → M) :
    ∑ j ∈ Finset.Ico 1 p, f j = ∑ k ∈ Finset.Icc 1 (p / 2), (f k + f (p - k)) := by
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  have hp2 : 2 ≤ p := by obtain ⟨q, rfl⟩ := hp; omega
  rw [Finset.sum_add_distrib]
  have hbij : ∑ k ∈ Finset.Icc 1 (p / 2), f (p - k) =
      ∑ k ∈ Finset.Icc (p / 2 + 1) (p - 1), f k := by
    refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢
      obtain ⟨q, rfl⟩ := hp; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢
      obtain ⟨q, rfl⟩ := hp; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk
      exact Nat.sub_sub_self (by omega)
    · intro k hk; simp only [Finset.mem_Icc] at hk
      exact Nat.sub_sub_self (by omega)
    · intros; rfl
  rw [hbij, ← Finset.sum_union]
  · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
  · rw [Finset.disjoint_left]
    intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega

end Toric

end Orb

open Orb in
open scoped Classical in
theorem solution
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    (tateLaurent K).veluX ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k))
        (toricPoint K 1 c).1 =
      ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).1 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).1 ∧
    (tateLaurent K).veluY ((Finset.Icc 1 (ℓ / 2)).image fun k => toricPoint K 1 (ζ ^ k))
        (toricPoint K 1 c).1 (toricPoint K 1 c).2 =
      ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).2 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).2 := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓ3 : 3 ≤ ℓ := by
    rcases hodd with ⟨t, rfl⟩
    have := hℓ.two_le; omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hℓ.ne_zero
  have hc1 : c ≠ 1 := fun h => hcℓ (by rw [h, one_pow])

  set W := tateLaurent K with hW
  set X : K → LaurentSeries K := fun u => (toricPoint K 1 u).1 with hXdef
  set Y : K → LaurentSeries K := fun u => (toricPoint K 1 u).2 with hYdef
  have hXu : ∀ u, (toricPoint K 1 u).1 = X u := fun u => rfl
  have hYu : ∀ u, (toricPoint K 1 u).2 = Y u := fun u => rfl
  have hPu : ∀ u, toricPoint K 1 u = (X u, Y u) := fun u => rfl

  have T := toricPoint_add_toricPoint_of_charZero K

  have hzpow : ∀ j : ℕ, 0 < j → j < ℓ → ζ ^ j ≠ 1 := fun j h1 h2 =>
    hζ.pow_ne_one_of_pos_of_lt h1.ne' h2
  have hzjℓ : ∀ j : ℕ, (ζ ^ j) ^ ℓ = 1 := fun j => by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hcz : ∀ j : ℕ, c * ζ ^ j ≠ 1 := by
    intro j h
    apply hcℓ
    have : (c * ζ ^ j) ^ ℓ = c ^ ℓ := by rw [mul_pow, hzjℓ, mul_one]
    rw [← this, h, one_pow]
  have hcne : ∀ j : ℕ, c ≠ ζ ^ j := by
    intro j h
    exact hcℓ (by rw [h, hzjℓ])

  have key : ∀ k ∈ Finset.Icc 1 (ℓ / 2),
      X c ≠ X (ζ ^ k) ∧
      X (ζ ^ (ℓ - k)) = X (ζ ^ k) ∧
      Y (ζ ^ (ℓ - k)) = W.toAffine.negY (X (ζ ^ k)) (Y (ζ ^ k)) ∧
      W.toAffine.Equation (X c) (Y c) ∧ W.toAffine.Equation (X (ζ ^ k)) (Y (ζ ^ k)) ∧
      W.toAffine.addX (X c) (X (ζ ^ k)) (W.toAffine.slope (X c) (X (ζ ^ k)) (Y c) (Y (ζ ^ k))) =
        X (c * ζ ^ k) ∧
      W.toAffine.addY (X c) (X (ζ ^ k)) (Y c) (W.toAffine.slope (X c) (X (ζ ^ k)) (Y c) (Y (ζ ^ k))) =
        Y (c * ζ ^ k) ∧
      W.toAffine.addX (X c) (X (ζ ^ k))
          (W.toAffine.slope (X c) (X (ζ ^ k)) (Y c) (W.toAffine.negY (X (ζ ^ k)) (Y (ζ ^ k)))) =
        X (c * ζ ^ (ℓ - k)) ∧
      W.toAffine.addY (X c) (X (ζ ^ k)) (Y c)
          (W.toAffine.slope (X c) (X (ζ ^ k)) (Y c) (W.toAffine.negY (X (ζ ^ k)) (Y (ζ ^ k)))) =
        Y (c * ζ ^ (ℓ - k)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hkℓ : k < ℓ := by omega
    have hk' : 0 < ℓ - k := by omega
    have hk'ℓ : ℓ - k < ℓ := by omega
    set z := ζ ^ k with hz
    set z' := ζ ^ (ℓ - k) with hz'
    have hz0 : z ≠ 0 := pow_ne_zero _ hζ0
    have hz'0 : z' ≠ 0 := pow_ne_zero _ hζ0
    have hz1 : z ≠ 1 := hzpow k (by omega) hkℓ
    have hz'1 : z' ≠ 1 := hzpow (ℓ - k) hk' hk'ℓ
    have hzz' : z * z' = 1 := by
      rw [hz, hz', ← pow_add, Nat.add_sub_cancel' hkℓ.le, hζ.pow_eq_one]
    have hxz : X c ≠ X z := toricPoint_fst_ne K 1 hc1 hz1 (hcne k) (hcz k)
    have hxz' : X c ≠ X z' := toricPoint_fst_ne K 1 hc1 hz'1 (hcne (ℓ - k)) (hcz (ℓ - k))

    obtain ⟨hPz, hPz', hzero, -⟩ := T z z' hz0 hz'0 hz1 hz'1
    have hneg := eq_neg_of_add_eq_zero_right (hzero hzz')
    rw [Affine.Point.neg_some] at hneg
    obtain ⟨hXz', hYz'⟩ := Affine.Point.some.inj hneg

    obtain ⟨hPc, hPz2, -, hadd⟩ := T c z hc0 hz0 hc1 hz1
    obtain ⟨hPcz, hsum⟩ := hadd (hcz k)
    rw [Affine.Point.add_of_X_ne hxz] at hsum
    obtain ⟨hX1, hY1⟩ := Affine.Point.some.inj hsum

    obtain ⟨hPc2, hPz'2, -, hadd'⟩ := T c z' hc0 hz'0 hc1 hz'1
    obtain ⟨hPcz', hsum'⟩ := hadd' (hcz (ℓ - k))
    rw [Affine.Point.add_of_X_ne hxz'] at hsum'
    obtain ⟨hX2, hY2⟩ := Affine.Point.some.inj hsum'
    simp only [hXu, hYu] at hXz' hYz' hX1 hY1 hX2 hY2 hPc hPz
    rw [hXz', hYz'] at hX2 hY2
    exact ⟨hxz, hXz', hYz', hPc.1, hPz.1, hX1, hY1, hX2, hY2⟩

  have hinj : ∀ k ∈ Finset.Icc 1 (ℓ / 2), ∀ k' ∈ Finset.Icc 1 (ℓ / 2),
      toricPoint K 1 (ζ ^ k) = toricPoint K 1 (ζ ^ k') → k = k' := by
    intro k hk k' hk' h
    rw [Finset.mem_Icc] at hk hk'
    by_contra hne
    have h1 : ζ ^ k ≠ ζ ^ k' := fun e => hne (hζ.pow_inj (by omega) (by omega) e)
    have h2 : ζ ^ k * ζ ^ k' ≠ 1 := by
      rw [← pow_add]; exact hzpow (k + k') (by omega) (by omega)
    exact toricPoint_fst_ne K 1 (hzpow k (by omega) (by omega)) (hzpow k' (by omega) (by omega)) h1 h2
      (congrArg Prod.fst h)
  have hrange : ∀ f : ℕ → LaurentSeries K,
      ∑ j ∈ Finset.range ℓ, f j = f 0 + ∑ j ∈ Finset.Ico 1 ℓ, f j := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hℓ.pos]
  refine ⟨?_, ?_⟩
  ·
    unfold WeierstrassCurve.veluX
    rw [Finset.sum_image hinj]
    have hterm : ∀ k ∈ Finset.Icc 1 (ℓ / 2),
        W.veluT (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2 / (X c - (toricPoint K 1 (ζ ^ k)).1) +
          W.veluU (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2 / (X c - (toricPoint K 1 (ζ ^ k)).1) ^ 2 =
        (X (c * ζ ^ k) + X (c * ζ ^ (ℓ - k))) - (X (ζ ^ k) + X (ζ ^ (ℓ - k))) := by
      intro k hk
      obtain ⟨hxz, hXz', -, hPc, hPz, hX1, -, hX2, -⟩ := key k hk
      rw [hXu, hYu, pair_x W hPc hPz hxz, hX1, hX2, hXz']
      ring
    rw [hXu, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      ← sum_Ico_eq_sum_half_pair ℓ hodd (fun j => X (c * ζ ^ j)),
      ← sum_Ico_eq_sum_half_pair ℓ hodd (fun j => X (ζ ^ j)), hrange, pow_zero, mul_one]
    simp only [hXu]
    ring
  ·
    unfold WeierstrassCurve.veluY
    rw [Finset.sum_image hinj]
    have hterm : ∀ k ∈ Finset.Icc 1 (ℓ / 2),
        (W.veluU (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2 * (2 * Y c + W.a₁ * X c + W.a₃) /
              (X c - (toricPoint K 1 (ζ ^ k)).1) ^ 3 +
            W.veluT (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2 *
                (W.a₁ * (X c - (toricPoint K 1 (ζ ^ k)).1) + Y c - (toricPoint K 1 (ζ ^ k)).2) /
              (X c - (toricPoint K 1 (ζ ^ k)).1) ^ 2 +
          (W.a₁ * W.veluU (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2 -
              W.veluGx (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2 *
                W.veluGy (toricPoint K 1 (ζ ^ k)).1 (toricPoint K 1 (ζ ^ k)).2) /
            (X c - (toricPoint K 1 (ζ ^ k)).1) ^ 2) =
        -((Y (c * ζ ^ k) + Y (c * ζ ^ (ℓ - k))) - (Y (ζ ^ k) + Y (ζ ^ (ℓ - k)))) := by
      intro k hk
      obtain ⟨hxz, -, hYz', hPc, hPz, -, hY1, -, hY2⟩ := key k hk
      rw [hXu, hYu, ← neg_eq_iff_eq_neg, pair_y W hPc hPz hxz, hY1, hY2, hYz']
      ring
    rw [hXu, hYu, Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
      ← sum_Ico_eq_sum_half_pair ℓ hodd (fun j => Y (c * ζ ^ j)),
      ← sum_Ico_eq_sum_half_pair ℓ hodd (fun j => Y (ζ ^ j)), hrange, pow_zero, mul_one]
    simp only [hYu]
    ring

end S_ModularCurve_veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico
end P2MW
export P2MW.S_ModularCurve_veluX_and_veluY_tateLaurent_toricPoint_eq_sum_range_sub_sum_Ico (solution)
