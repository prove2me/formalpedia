-- Prove2me | solution 1 for GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:58.695863+00:00
-- url     : https://prove2.me/submissions/8c96b9c6-5ca6-4368-9f07-e26086adfd82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageConnectedComponentRationalPointFieldExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageConnectedComponentRationalPointFieldExtStatement
import Theorems.Thm_GlobalTheory_preimage_connectedComponent_rationalPoint_baseChange


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
theorem _root_.solution : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  first | exact @GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange | exact GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange | (intros; apply GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange <;> assumption)
end _root_.GlobalTheory.T
