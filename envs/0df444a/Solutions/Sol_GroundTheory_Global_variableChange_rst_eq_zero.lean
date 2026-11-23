-- Prove2me | solution 1 for GroundTheory.Global.variableChange_rst_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:38.731165+00:00
-- url     : https://prove2.me/submissions/fc506186-da9a-4653-a996-f6bb533aef0a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
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
theorem _root_.solution {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have h1 := hCW.a₁_eq
  have h2 := hCW.a₂_eq
  have h3 := hCW.a₃_eq
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, hW.a₁_eq, hW.a₂_eq,
    hW.a₃_eq] at h1 h2 h3
  have hs : C.s = 0 := by simpa [hv] using h1
  have ht : C.t = 0 := by simpa [hv] using h3
  have hr : C.r = 0 := by simpa [hv, hs] using h2
  exact ⟨hr, hs, ht⟩
end GroundTheory.Global
