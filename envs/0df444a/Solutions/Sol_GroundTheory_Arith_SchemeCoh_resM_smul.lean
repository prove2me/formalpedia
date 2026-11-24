-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.resM_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:49.684331+00:00
-- url     : https://prove2.me/submissions/e31695b0-5df0-4751-af26-84af308b263e

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
theorem _root_.solution (P : PMod X) {U V : X.Opens} (h : V ≤ U) (r : ringOn X U) (x : P.obj (op U)) :
    resM P h (r • x) = resR h r • resM P h x :=
  PresheafOfModules.map_smul _ _ _ _
end GroundTheory.Arith.SchemeCoh
