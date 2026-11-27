-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.H.endRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:29.391917+00:00
-- url     : https://prove2.me/submissions/aef3504b-a3a8-47ac-959d-6f1f13b66707

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
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
namespace GroundTheory.Arith.SchemeCoh
namespace H
theorem _root_.solution (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (f : End G)
    (x : Sheaf.H.{w'} G n) : H.endRingHom G n f x = Sheaf.H.map f n x := rfl
end H
end GroundTheory.Arith.SchemeCoh
