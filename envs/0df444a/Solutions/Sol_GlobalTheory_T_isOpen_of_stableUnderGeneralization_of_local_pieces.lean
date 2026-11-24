-- Prove2me | solution 1 for GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:33.823486+00:00
-- url     : https://prove2.me/submissions/6ec5bea4-eeab-4728-b979-d1ee67e077da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Theorems.Thm_GlobalTheory_isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces


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
theorem _root_.solution : ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces <;> assumption)
end _root_.GlobalTheory.T
