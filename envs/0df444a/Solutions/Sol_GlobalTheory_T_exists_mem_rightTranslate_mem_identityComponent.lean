-- Prove2me | solution 1 for GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:35:56.859604+00:00
-- url     : https://prove2.me/submissions/4c8fab55-d22b-4bee-9fe2-126ebf483c87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponentStatement
import Theorems.Thm_GlobalTheory_exists_mem_and_rightTranslate_mem_of_mem_identityComponent


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
theorem _root_.solution : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  first | exact @GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | exact GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent | (intros; apply GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent <;> assumption)
end _root_.GlobalTheory.T
