-- Prove2me | solution 1 for GroundTheory.Global.variableChangePoint_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:51.418402+00:00
-- url     : https://prove2.me/submissions/8ead7e09-2fe3-484a-9e9a-84020b21e00d

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
    (hC : C • W = W') : variableChangePoint C hC .zero = .zero := rfl
end GroundTheory.Global
