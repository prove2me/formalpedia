-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.resM_resM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:24:52.852536+00:00
-- url     : https://prove2.me/submissions/31aa1fe6-77b4-4a82-9514-849351d26b59

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
theorem _root_.solution (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (x : P.obj (op U)) :
    resM P i (resM P h x) = resM P (i.trans h) x := by
  rw [resM, resM, resM, ← PresheafOfModules.map_comp_apply]
  rfl
end GroundTheory.Arith.SchemeCoh
