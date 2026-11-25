-- Prove2me | solution 1 for GroundTheory.Global.weberFunction_variableChangePoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:51.334262+00:00
-- url     : https://prove2.me/submissions/61f90144-89e9-4c21-9161-d887bc311a23

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
import Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
import Theorems.Thm_GroundTheory_Global_weberValue_of_ne_zero
import Theorems.Thm_GroundTheory_Global_variableChange_rst_eq_zero
import Theorems.Thm_P2M_GroundTheory_Global_variableChange_a__of_isShortForm_97ca09bc4117
import Theorems.Thm_P2M_GroundTheory_Global_variableChange_a__of_isShortForm_87451d3b79c6
import Theorems.Thm_GroundTheory_Global_variableChangePoint_some
import Theorems.Thm_GroundTheory_Global_variableChangePoint_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.variableChangePoint_zero


attribute [local simp] GroundTheory.Global.weberFunction_zero
attribute [local simp] GroundTheory.Global.weberFunction_some

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
variable [CharZero F]
namespace GroundTheory.Global
theorem _root_.solution (C : VariableChange F) {W W' : WeierstrassCurve F}
    [W.IsElliptic] (hC : C • W = W') (hW : IsShortForm W) (hW' : IsShortForm W')
    (P : W.toAffine.Point) :
    weberFunction W' (variableChangePoint C hC P) = weberFunction W P := by
  subst hC
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hW'
  cases P with
  | zero => rfl
  | some x y h =>
    rw [variableChangePoint_some, weberFunction_some, weberFunction_some]
    congr 1
    have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have ha := variableChange_a₄_of_isShortForm hW hW'
    have hb := variableChange_a₆_of_isShortForm hW hW'
    have hb0 : (C • W).a₆ = 0 ↔ W.a₆ = 0 := by rw [hb]; simp
    have ha0 : (C • W).a₄ = 0 ↔ W.a₄ = 0 := by rw [ha]; simp
    by_cases h6 : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (hb0.mpr h6), weberValue_of_a₆_eq_zero h6]
      simp only [g₂, ha, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    by_cases h4 : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (ha0.mpr h4) (mt hb0.mp h6), weberValue_of_a₄_eq_zero h4 h6]
      simp only [g₃, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    · rw [weberValue_of_ne_zero (mt ha0.mp h4) (mt hb0.mp h6), weberValue_of_ne_zero h4 h6]
      simp only [g₂, g₃, ha, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
end GroundTheory.Global
