-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.tensorLift_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:30.383624+00:00
-- url     : https://prove2.me/submissions/e479d053-7cc5-4e07-8a14-601715ea858e

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
    (e : (preMod X).obj M ⊗ (preMod X).obj N ⟶ (preMod X).obj G) (f : M ⊗ N ⟶ G)
    (hf : tensorToSheaf M N ≫ (preMod X).map f = e) : f = tensorLift e := by
  rw [← hf, tensorLift, tensorToSheaf, Category.assoc, ← Functor.map_comp,
    ← Adjunction.homEquiv_unit, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
end GroundTheory.Arith.SchemeCoh
