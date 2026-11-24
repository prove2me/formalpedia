-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.app_resM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:46.913491+00:00
-- url     : https://prove2.me/submissions/409b0524-1dde-4490-a495-6327744db662

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
theorem _root_.solution {P Q : PMod X} (φ : P ⟶ Q) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) :
    φ.app (op V) (resM P h x) = resM Q h (φ.app (op U) x) :=
  PresheafOfModules.naturality_apply φ _ x
end GroundTheory.Arith.SchemeCoh
