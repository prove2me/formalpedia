-- Prove2me | solution 1 for GlobalTheory.T.exists_lift_algebraically_closed_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:16.237667+00:00
-- url     : https://prove2.me/submissions/5407373d-01a4-4249-baeb-1450371b2ffc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftAlgebraicallyClosedPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftAlgebraicallyClosedPointStatement
import Theorems.Thm_GlobalTheory_exists_lift_of_range_subset_of_isAlgClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  first | exact @GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed | exact GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed | (intros; apply GlobalTheory.exists_lift_of_range_subset_of_isAlgClosed <;> assumption)
end _root_.GlobalTheory.T
