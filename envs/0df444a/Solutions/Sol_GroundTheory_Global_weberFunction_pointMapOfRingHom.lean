-- Prove2me | solution 1 for GroundTheory.Global.weberFunction_pointMapOfRingHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:25.682113+00:00
-- url     : https://prove2.me/submissions/a2341bf8-799d-4c6e-99c3-5a635a0f4cd6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_1cba6dac3294
import Theorems.Thm_P2M_GroundTheory_Global_weberValue_of_a__eq_zero_6d58591c3e51
import Theorems.Thm_GroundTheory_Global_weberValue_of_ne_zero
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
variable {L : Type*} [Field L]
namespace GroundTheory.Global
theorem _root_.solution (φ : F →+* L) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    weberFunction (W.map φ) (pointMapOfRingHom φ P) = OnePoint.map φ (weberFunction W P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    have h4 : (W.map φ).a₄ = φ W.a₄ := rfl
    have h6 : (W.map φ).a₆ = φ W.a₆ := rfl
    show OnePoint.some _ = OnePoint.some _
    congr 1
    by_cases hb : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (by rw [h6, hb, map_zero]), weberValue_of_a₆_eq_zero hb]
      simp [g₂, map_Δ, map_ofNat]
    have hb' : (W.map φ).a₆ ≠ 0 := by rw [h6]; exact (map_ne_zero φ).mpr hb
    by_cases ha : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (by rw [h4, ha, map_zero]) hb', weberValue_of_a₄_eq_zero ha hb]
      simp [g₃, map_Δ, map_ofNat]
    · have ha' : (W.map φ).a₄ ≠ 0 := by rw [h4]; exact (map_ne_zero φ).mpr ha
      rw [weberValue_of_ne_zero ha' hb', weberValue_of_ne_zero ha hb]
      simp [g₂, g₃, map_Δ, map_ofNat]
end GroundTheory.Global
