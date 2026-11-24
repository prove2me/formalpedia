-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.W_tensorToSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:29:19.334799+00:00
-- url     : https://prove2.me/submissions/a13003e5-96ca-49da-a549-32ce7da2d906

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
theorem _root_.solution (M N : X.Modules) :
    ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj (tensorToSheaf M N) := by
  refine MorphismProperty.comp_mem _ _ _ ?_ (MorphismProperty.of_isIso _ _)
  change (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map _)
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact GrothendieckTopology.W_toSheafify _ _
end GroundTheory.Arith.SchemeCoh
