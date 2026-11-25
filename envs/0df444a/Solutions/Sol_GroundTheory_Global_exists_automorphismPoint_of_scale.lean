-- Prove2me | solution 1 for GroundTheory.Global.exists_automorphismPoint_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:46.393801+00:00
-- url     : https://prove2.me/submissions/ec3cb83c-a219-44b4-8b67-2247ec7b6f58

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
import Theorems.Thm_GroundTheory_Global_automorphismEquivRootsOfUnity_apply
import Theorems.Thm_GroundTheory_Global_variableChangePoint_some
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
omit [W.IsElliptic]
namespace GroundTheory.Global
theorem _root_.solution (hW : IsShortForm W) {v x₁ y₁ x₂ y₂ : F} (hv : v ≠ 0)
    (h4 : v ^ 4 * W.a₄ = W.a₄) (h6 : v ^ 6 * W.a₆ = W.a₆) (hx : v ^ 2 * x₁ = x₂)
    (hy : v ^ 3 * y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    ∃ ξ : MulAction.stabilizer (VariableChange F) W,
      automorphismPoint ξ (.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by
  obtain ⟨ξ, hξ⟩ := (mem_range_automorphismScale hW ((Units.mk0 v hv)⁻¹)).mpr
    ⟨by simpa using h4, by simpa using h6⟩
  refine ⟨ξ, ?_⟩
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  have hu : (↑ξ.1.u⁻¹ : F) = v := by
    have : ξ.1.u = (Units.mk0 v hv)⁻¹ := hξ
    rw [this, inv_inv, Units.val_mk0]
  simp only [automorphismPoint, variableChangePoint_some, hr, hs, ht, hu, sub_zero, zero_mul,
    Affine.Point.some.injEq]
  exact ⟨hx, hy⟩
end GroundTheory.Global
