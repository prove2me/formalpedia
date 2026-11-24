-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.tensorToSheaf_tensorLift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:44.870903+00:00
-- url     : https://prove2.me/submissions/d6087550-a4f8-4eb2-a15d-5704f245e7ef

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
theorem _root_.solution {M N G : X.Modules}
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) :
    tensorToSheaf M N ≫ (preMod X).map (tensorLift e) = e := by
  rw [tensorToSheaf, tensorLift, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
end GroundTheory.Arith.SchemeCoh
