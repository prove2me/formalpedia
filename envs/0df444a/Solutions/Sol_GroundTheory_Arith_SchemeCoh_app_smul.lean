-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.app_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:46.964589+00:00
-- url     : https://prove2.me/submissions/5e61a4e5-2aa5-4965-9f62-862acc564206

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
theorem _root_.solution {P Q : PMod X} (φ : P ⟶ Q) {U : X.Opens} (r : ringOn X U) (x : P.obj (op U)) :
    φ.app (op U) (r • x) = r • φ.app (op U) x :=
  (φ.app (op U)).hom.map_smul r x
end GroundTheory.Arith.SchemeCoh
