-- Prove2me | solution 1 for GroundTheory.Global.variableChangePoint_some
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:34.37944+00:00
-- url     : https://prove2.me/submissions/2b8d0b54-68b6-4fc4-935a-14c509d5aa92

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open WeierstrassCurve
variable {F : Type*} [Field F]
namespace GroundTheory.Global
theorem _root_.solution (C : VariableChange F) {W W' : WeierstrassCurve F}
    (hC : C • W = W') {x y : F} (h : W.toAffine.Nonsingular x y) :
    variableChangePoint C hC (.some x y h) =
      .some (↑C.u⁻¹ ^ 2 * (x - C.r)) (↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        (by subst hC; exact nonsingular_variableChange C W h) := rfl
end GroundTheory.Global
