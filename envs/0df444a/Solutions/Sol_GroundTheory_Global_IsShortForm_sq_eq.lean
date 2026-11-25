-- Prove2me | solution 1 for GroundTheory.Global.IsShortForm.sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:18.494581+00:00
-- url     : https://prove2.me/submissions/9a2241e9-4885-40f3-9f7b-92b8a050934f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
import Theorems.Thm_GroundTheory_Global_automorphismEquivRootsOfUnity_apply
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
omit [CharZero F] [W.IsElliptic]
namespace GroundTheory.Global
namespace IsShortForm
theorem _root_.solution (hW : IsShortForm W) {x y : F} (h : W.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  have := h.1
  rw [Affine.equation_iff] at this
  simpa [hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using this
end IsShortForm
end GroundTheory.Global
