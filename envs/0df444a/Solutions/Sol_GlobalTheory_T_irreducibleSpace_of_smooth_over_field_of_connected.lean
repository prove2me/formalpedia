-- Prove2me | solution 1 for GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:18.861113+00:00
-- url     : https://prove2.me/submissions/d27657b5-a38a-4fae-adfe-5a0dd2372536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement
import Theorems.Thm_GlobalTheory_irreducibleSpace_of_smooth_field_of_connectedSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f → ConnectedSpace X → IrreducibleSpace X := by
  first | exact @GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace | (intros; apply GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace <;> assumption)
end _root_.GlobalTheory.T
