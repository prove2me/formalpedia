-- Prove2me | solution 1 for GroundTheory.Global.weberFunction_automorphismPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:28.835278+00:00
-- url     : https://prove2.me/submissions/26b35864-d26b-43f3-aa1f-26147a933025

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms
import Theorems.Thm_GroundTheory_Global_weberFunction_variableChangePoint


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
open WeierstrassCurve OnePoint ShortWeierstrass
variable {F : Type*} [Field F]
variable [CharZero F] {W : WeierstrassCurve F}
variable [W.IsElliptic]
namespace GroundTheory.Global
theorem _root_.solution (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) (P : W.toAffine.Point) :
    weberFunction W (automorphismPoint ξ P) = weberFunction W P :=
  weberFunction_variableChangePoint ξ.1 _ hW hW P
end GroundTheory.Global
