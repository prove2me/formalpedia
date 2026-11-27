-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.smulAbRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:21.601648+00:00
-- url     : https://prove2.me/submissions/c43fb834-41a9-403e-b891-a4be1bd72290

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
universe w' w v u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (F : X.Modules) (r : Γ(X, ⊤)) :
    smulAbRingHom F r = (SheafOfModules.toSheaf X.ringCatSheaf).map (smulHom F r) := rfl
end GroundTheory.Arith.SchemeCoh
