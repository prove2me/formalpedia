-- Prove2me | solution 2 for GroundTheory.Arith.SchemeCoh.app_smul
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:44:58.122036+00:00
-- url     : https://prove2.me/submissions/58cd1f75-e348-49db-b57a-dd339f3505a8

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


theorem solution {P Q : PMod X} (φ : P ⟶ Q) {U : X.Opens} (r : ringOn X U) (x : P.obj (op U)) :
    φ.app (op U) (r • x) = r • φ.app (op U) x := by
  first | exact (φ.app (op U)).hom.map_smul r x | exact (φ.app (op U)).map_smul r x
