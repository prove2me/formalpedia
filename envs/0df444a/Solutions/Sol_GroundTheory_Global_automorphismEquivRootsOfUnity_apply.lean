-- Prove2me | solution 1 for GroundTheory.Global.automorphismEquivRootsOfUnity_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:56.349122+00:00
-- url     : https://prove2.me/submissions/29039b9c-477a-4907-b4d3-a453371ed131

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunction
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_WeberFunctionAutomorphisms

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
    (ξ : MulAction.stabilizer (VariableChange F) W) :
    ((automorphismEquivRootsOfUnity hW ξ : Fˣ)) = ξ.1.u := rfl
end GroundTheory.Global
