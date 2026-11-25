-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.resM_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:57.321082+00:00
-- url     : https://prove2.me/submissions/3945a532-6d23-4065-9b66-a1fd709aa4a6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf

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
theorem _root_.solution (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x y : P.obj (op U)) :
    resM P h (x + y) = resM P h x + resM P h y :=
  map_add _ _ _
end GroundTheory.Arith.SchemeCoh
