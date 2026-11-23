-- Prove2me | solution 1 for GroundTheory.Global.weberFunction_some
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:12.989625+00:00
-- url     : https://prove2.me/submissions/340711a6-8f18-444b-a609-fd54960c01d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_VariableChangePoints
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open WeierstrassCurve OnePoint
variable {F : Type*} [Field F]
open ShortWeierstrass
namespace GroundTheory.Global
theorem _root_.solution (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    weberFunction W (.some x y h) = OnePoint.some (weberValue W x) := rfl
end GroundTheory.Global
