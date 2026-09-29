-- Prove2me | solution 1 for ModularCurve.IsGamma1Point.existsUnique_variableChange_isNormalForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/703a3c8f-c8d9-5cbf-aca9-8f59b7521463

import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelNormalForm
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Theorems.Thm_WeierstrassCurve_eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "indepElt LevelPData LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ IsNormalForm isNormalForm_of_ne_three IsGamma1Point"
namespace LevelNormalFormBodyG1
p2m_open "ModularCurve"

open WeierstrassCurve Polynomial

variable {T : Type u} [CommRing T]

theorem eval_Ψ₂Sq (W : WeierstrassCurve T) (x : T) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [WeierstrassCurve.Ψ₂Sq]

theorem eval_Ψ₃ (W : WeierstrassCurve T) (x : T) :
    W.Ψ₃.eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp [WeierstrassCurve.Ψ₃]

theorem psi2_sq_eq_eval_Ψ₂Sq (W : WeierstrassCurve T) {x y : T} (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [eval_Ψ₂Sq]
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  linear_combination (4 : T) * h

theorem isUnit_psi2 (W : WeierstrassCurve T) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (hu : IsUnit ((ℓ : T) * W.Δ)) {x y : T} (heq : W.toAffine.Equation x y)
    (hx : (W.preΨ ℓ).eval x = 0) : IsUnit (2 * y + W.a₁ * x + W.a₃) := by
  have h2 : ¬ (ℓ : ℤ) ∣ 2 := by
    intro h
    have : (ℓ : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h
    omega
  have key := (W.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (p := ℓ) (by omega) hu
    hx h2).1
  rw [WeierstrassCurve.ΨSq_two, ← psi2_sq_eq_eval_Ψ₂Sq W heq] at key
  exact (isUnit_pow_iff two_ne_zero).mp key

theorem isUnit_eval_Ψ₃ (W : WeierstrassCurve T) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (hℓ : ℓ ≠ 3) (hu : IsUnit ((ℓ : T) * W.Δ)) {x : T} (hx : (W.preΨ ℓ).eval x = 0) :
    IsUnit (W.Ψ₃.eval x) := by
  have h3 : ¬ (ℓ : ℤ) ∣ 3 := by
    intro h
    have h' : ℓ ∣ 3 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h'
    (interval_cases ℓ; simp_all)
  have key := (W.eval_prePsi_Phi_div_PsiSq_eq_zero_of_eval_prePsi_eq_zero (p := ℓ) (by omega) hu
    hx h3).1
  rw [WeierstrassCurve.ΨSq_three, eval_pow] at key
  exact (isUnit_pow_iff two_ne_zero).mp key

theorem eval_Ψ₃_variableChange (W : WeierstrassCurve T) (C : VariableChange T) (x : T) :
    (C • W).Ψ₃.eval (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Tˣ) : T) ^ 8 * W.Ψ₃.eval x := by
  rw [eval_Ψ₃, eval_Ψ₃, WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆, WeierstrassCurve.variableChange_b₈]
  ring

theorem isUnit_sub_of_isUnit_indepElt (W : WeierstrassCurve T) {ℓ : ℕ} (hℓ3 : 3 ≤ ℓ) {x₀ x : T}
    (h : IsUnit (indepElt W ℓ x₀ x)) : IsUnit (x - x₀) := by
  unfold indepElt at h
  have h1 : 1 ∈ Finset.Icc 1 ((ℓ - 1) / 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [← Finset.mul_prod_erase _ _ h1] at h
  have h' := isUnit_of_mul_isUnit_left h
  simpa [WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one] using h'

theorem isUnit_y_of_deuring (W : WeierstrassCurve T) {x y : T} (h2 : W.a₂ = 0) (h4 : W.a₄ = 0)
    (h6 : W.a₆ = 0) (heq : W.toAffine.Equation x y) (hx : IsUnit x) : IsUnit y := by
  simp only [WeierstrassCurve.Affine.equation_iff, h2, h4, h6] at heq
  have e : y * (y + W.a₁ * x + W.a₃) = x ^ 3 := by linear_combination heq
  have hu : IsUnit (y * (y + W.a₁ * x + W.a₃)) := by rw [e]; exact hx.pow 3
  exact isUnit_of_mul_isUnit_left hu

theorem forced (W : WeierstrassCurve T) (D : LevelPData T) (C : VariableChange T)
    (hx : (D.variableChange C).xP = 0) (hy : (D.variableChange C).yP = 0) (h4 : (C • W).a₄ = 0) :
    C.r = D.xP ∧ C.t = D.yP ∧
      C.s * (2 * D.yP + W.a₁ * D.xP + W.a₃) =
        W.a₄ + 2 * D.xP * W.a₂ + 3 * D.xP ^ 2 - D.yP * W.a₁ := by
  have hv : IsUnit (((C.u⁻¹ : Tˣ) : T)) := Units.isUnit _
  rw [LevelPData.variableChange_xP] at hx
  rw [LevelPData.variableChange_yP] at hy
  rw [WeierstrassCurve.variableChange_a₄] at h4
  have hx' := ((hv.pow 2).mul_right_eq_zero).mp hx
  have hy' := ((hv.pow 3).mul_right_eq_zero).mp hy
  have h4' := ((hv.pow 4).mul_right_eq_zero).mp h4
  have hr : C.r = D.xP := by linear_combination (-1 : T) * hx'
  have ht : C.t = D.yP := by linear_combination (-1 : T) * hy' - C.s * hx'
  refine ⟨hr, ht, ?_⟩
  rw [hr, ht] at h4'
  linear_combination (-1 : T) * h4'

theorem coeffs (W : WeierstrassCurve T) (D : LevelPData T) (heq : W.toAffine.Equation D.xP D.yP)
    (C : VariableChange T) (hr : C.r = D.xP) (ht : C.t = D.yP)
    (hs : C.s * (2 * D.yP + W.a₁ * D.xP + W.a₃) =
      W.a₄ + 2 * D.xP * W.a₂ + 3 * D.xP ^ 2 - D.yP * W.a₁) :
    (C • W).a₄ = 0 ∧ (C • W).a₆ = 0 ∧ (D.variableChange C).xP = 0 ∧ (D.variableChange C).yP = 0 ∧
      (C • W).a₂ = ((C.u⁻¹ : Tˣ) : T) ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * D.xP - C.s ^ 2) ∧
      (C • W).a₃ = ((C.u⁻¹ : Tˣ) : T) ^ 3 * (2 * D.yP + W.a₁ * D.xP + W.a₃) ∧
      (D.variableChange C).xQ = ((C.u⁻¹ : Tˣ) : T) ^ 2 * (D.xQ - D.xP) ∧
      (D.variableChange C).yQ = ((C.u⁻¹ : Tˣ) : T) ^ 3 * (D.yQ - C.s * (D.xQ - D.xP) - D.yP) := by
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.variableChange_a₄, hr, ht]
    linear_combination (-(((C.u⁻¹ : Tˣ) : T) ^ 4)) * hs
  · rw [WeierstrassCurve.variableChange_a₆, hr, ht]
    linear_combination (-(((C.u⁻¹ : Tˣ) : T) ^ 6)) * heq
  · rw [LevelPData.variableChange_xP, hr]
    ring
  · rw [LevelPData.variableChange_yP, hr, ht]
    ring
  · rw [WeierstrassCurve.variableChange_a₂, hr]
  · rw [WeierstrassCurve.variableChange_a₃, hr, ht]
    ring
  · rw [LevelPData.variableChange_xQ, hr]
  · rw [LevelPData.variableChange_yQ, hr, ht]

theorem eval_Ψ₃_eq (W : WeierstrassCurve T) (D : LevelPData T) (heq : W.toAffine.Equation D.xP D.yP)
    (σ : T) (hs : σ * (2 * D.yP + W.a₁ * D.xP + W.a₃) =
      W.a₄ + 2 * D.xP * W.a₂ + 3 * D.xP ^ 2 - D.yP * W.a₁) :
    W.Ψ₃.eval D.xP =
      (W.a₂ - σ * W.a₁ + 3 * D.xP - σ ^ 2) * (2 * D.yP + W.a₁ * D.xP + W.a₃) ^ 2 := by
  obtain ⟨h4, h6, -, -, h2, h3, -, -⟩ :=
    coeffs W D heq ⟨1, D.xP, σ, D.yP⟩ rfl rfl hs
  have h := eval_Ψ₃_variableChange W ⟨1, D.xP, σ, D.yP⟩ D.xP
  simp only [inv_one, Units.val_one, one_pow, one_mul, sub_self, mul_zero] at h h2 h3
  rw [← h, eval_Ψ₃]
  simp only [WeierstrassCurve.b₈, h4, h6, h2, h3]
  ring

end ModularCurve.LevelNormalFormBodyG1

open ModularCurve.LevelNormalFormBodyG1 in

theorem solution
    {T : Type u} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (W : WeierstrassCurve T) (hu : IsUnit ((ℓ : T) * W.Δ)) (D : LevelPData T) (hD : IsGamma1Point W ℓ D) :
    ∃! C : WeierstrassCurve.VariableChange T, IsNormalForm ℓ (C • W) (D.variableChange C) := by
  have hℓ3 : 3 ≤ ℓ := by omega

  obtain ⟨ψu, hψu⟩ := isUnit_psi2 W hℓ3 hu hD.equation_P hD.preΨ_P
  have hψinv : (2 * D.yP + W.a₁ * D.xP + W.a₃) * ((ψu⁻¹ : Tˣ) : T) = 1 := by
    rw [← hψu, Units.mul_inv]
  have hσ : (W.a₄ + 2 * D.xP * W.a₂ + 3 * D.xP ^ 2 - D.yP * W.a₁) * ((ψu⁻¹ : Tˣ) : T) *
      (2 * D.yP + W.a₁ * D.xP + W.a₃) = W.a₄ + 2 * D.xP * W.a₂ + 3 * D.xP ^ 2 - D.yP * W.a₁ := by
    rw [← hψu, mul_assoc, Units.inv_mul, mul_one]
  generalize hσdef : (W.a₄ + 2 * D.xP * W.a₂ + 3 * D.xP ^ 2 - D.yP * W.a₁) * ((ψu⁻¹ : Tˣ) : T) = σ
    at hσ
  have hΨ₃ := eval_Ψ₃_eq W D hD.equation_P σ hσ

  have huniq : ∀ C : WeierstrassCurve.VariableChange T,
      (D.variableChange C).xP = 0 → (D.variableChange C).yP = 0 → (C • W).a₄ = 0 →
      C.r = D.xP ∧ C.t = D.yP ∧ C.s = σ := by
    intro C hx hy h4
    obtain ⟨hr, ht, hs⟩ := forced W D C hx hy h4
    refine ⟨hr, ht, ?_⟩
    have h0 : (C.s - σ) * (2 * D.yP + W.a₁ * D.xP + W.a₃) = 0 := by linear_combination hs - hσ
    rw [← hψu, Units.mul_left_eq_zero] at h0
    linear_combination h0
  have h3 : ℓ ≠ 3 := by omega

  have hαu : IsUnit (W.a₂ - σ * W.a₁ + 3 * D.xP - σ ^ 2) := by
    have h := isUnit_eval_Ψ₃ W hℓ3 h3 hu hD.preΨ_P
    rw [hΨ₃] at h
    exact isUnit_of_mul_isUnit_left h
  obtain ⟨αu, hαu⟩ := hαu

  have hv : ((αu * ψu⁻¹ : Tˣ) : T) * (2 * D.yP + W.a₁ * D.xP + W.a₃) =
      W.a₂ - σ * W.a₁ + 3 * D.xP - σ ^ 2 := by
    rw [Units.val_mul, ← hψu, mul_assoc, Units.inv_mul, mul_one, hαu]
  have hv' : ((αu * ψu⁻¹ : Tˣ) : T) = (W.a₂ - σ * W.a₁ + 3 * D.xP - σ ^ 2) * ((ψu⁻¹ : Tˣ) : T) := by
    rw [Units.val_mul, hαu]
  refine ⟨⟨(αu * ψu⁻¹)⁻¹, D.xP, σ, D.yP⟩, ?_, ?_⟩
  ·
    obtain ⟨h4, h6, hxP, hyP, h2, h3', -, -⟩ :=
      coeffs W D hD.equation_P ⟨(αu * ψu⁻¹)⁻¹, D.xP, σ, D.yP⟩ rfl rfl hσ
    rw [isNormalForm_of_ne_three h3]
    refine ⟨h4, h6, ?_, hxP, hyP⟩
    rw [h2, h3']
    dsimp only
    rw [inv_inv]
    linear_combination (-(((αu * ψu⁻¹ : Tˣ) : T) ^ 2)) * hv
  ·
    intro C hC
    rw [isNormalForm_of_ne_three h3] at hC
    obtain ⟨h4, -, h23, hx, hy⟩ := hC
    obtain ⟨hr, ht, hs⟩ := huniq C hx hy h4
    obtain ⟨-, -, -, -, h2, h3', -, -⟩ :=
      coeffs W D hD.equation_P C hr ht (by rw [hs]; exact hσ)
    rw [h2, h3', hs] at h23
    have h0 : ((C.u⁻¹ : Tˣ) : T) ^ 2 * ((W.a₂ - σ * W.a₁ + 3 * D.xP - σ ^ 2) -
        ((C.u⁻¹ : Tˣ) : T) * (2 * D.yP + W.a₁ * D.xP + W.a₃)) = 0 := by
      linear_combination h23
    rw [← Units.val_pow_eq_pow_val, Units.mul_right_eq_zero] at h0
    have hvC : ((C.u⁻¹ : Tˣ) : T) = ((αu * ψu⁻¹ : Tˣ) : T) := by
      rw [hv']
      linear_combination (-((ψu⁻¹ : Tˣ) : T)) * h0 - ((C.u⁻¹ : Tˣ) : T) * hψinv
    have huC : C.u = (αu * ψu⁻¹)⁻¹ := by
      rw [← inv_inv C.u, Units.ext hvC]
    exact WeierstrassCurve.VariableChange.ext huC hr hs ht

end S_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm
end P2MW
export P2MW.S_ModularCurve_IsGamma1Point_existsUnique_variableChange_isNormalForm (solution)
