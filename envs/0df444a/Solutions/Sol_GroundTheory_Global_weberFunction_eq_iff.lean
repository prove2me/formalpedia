-- Prove2me | solution 1 for GroundTheory.Global.weberFunction_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:22.755602+00:00
-- url     : https://prove2.me/submissions/a0a0f378-876e-4ed8-ae22-3184c8589ff2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
import Theorems.Thm_GroundTheory_Global_automorphismEquivRootsOfUnity_apply
import Theorems.Thm_GroundTheory_Global_weberFunction_automorphismPoint
import Theorems.Thm_GroundTheory_Global_IsShortForm_sq_eq
import Theorems.Thm_GroundTheory_Global_exists_scale_of_weberValue_eq
import Theorems.Thm_GroundTheory_Global_exists_automorphismPoint_of_scale
import Theorems.Thm_GroundTheory_Global_variableChangePoint_zero
import Theorems.Thm_GroundTheory_Global_weberFunction_some
import Theorems.Thm_GroundTheory_Global_weberFunction_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.variableChangePoint_zero
attribute [local simp] GroundTheory.Global.weberFunction_some
attribute [local simp] GroundTheory.Global.weberFunction_zero


attribute [local simp] GroundTheory.Global.automorphismEquivRootsOfUnity_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]
variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]
namespace GroundTheory.Global
theorem _root_.solution [IsAlgClosed F] (hW : IsShortForm W) (P Q : W.toAffine.Point) :
    weberFunction W P = weberFunction W Q ↔
      ∃ ξ : MulAction.stabilizer (VariableChange F) W, automorphismPoint ξ P = Q := by
  constructor
  · intro hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => exact ⟨1, rfl⟩
      | some x y h => simp at hPQ
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp at hPQ
      | some x₂ y₂ h₂ =>
        simp only [weberFunction_some] at hPQ
        have hx : weberValue W x₁ = weberValue W x₂ := Option.some_injective _ hPQ
        obtain ⟨v, hv, h4, h6, hx2⟩ := exists_scale_of_weberValue_eq hW hx
        have hy : y₂ ^ 2 = (v ^ 3 * y₁) ^ 2 := by
          rw [hW.sq_eq h₂, ← hx2]
          linear_combination (-(v ^ 6)) * hW.sq_eq h₁ - v ^ 2 * x₁ * h4 - h6
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
        · exact exists_automorphismPoint_of_scale hW hv h4 h6 hx2 hy.symm h₁ h₂
        · refine exists_automorphismPoint_of_scale (v := -v) hW (neg_ne_zero.mpr hv) ?_ ?_ ?_ ?_
            h₁ h₂
          · rw [show (-v) ^ 4 = v ^ 4 by ring, h4]
          · rw [show (-v) ^ 6 = v ^ 6 by ring, h6]
          · rw [show (-v) ^ 2 = v ^ 2 by ring, hx2]
          · rw [hy]
            ring
  · rintro ⟨ξ, rfl⟩
    exact (weberFunction_automorphismPoint hW ξ P).symm
end GroundTheory.Global
