-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.resM_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:19.221878+00:00
-- url     : https://prove2.me/submissions/70b81306-181e-40d4-beb8-3fa5f3265081

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (P : PMod X) {U : X.Opens} (x : P.obj (op U)) : resM P (le_refl U) x = x := by
  change P.map (𝟙 (op U)) x = x
  rw [PresheafOfModules.map_id]
  rfl
end GroundTheory.Arith.SchemeCoh
