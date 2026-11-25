-- Prove2me | solution 1 for GlobalTheory.T.exists_component_surjects_clopen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:57.603454+00:00
-- url     : https://prove2.me/submissions/9b3edbd7-d927-449d-8b88-7ad35f1262b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComponentSurjectsClopen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComponentSurjectsClopenStatement
import Theorems.Thm_GlobalTheory_clopen_image_irreducibleComponent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  first | exact @GlobalTheory.clopen_image_irreducibleComponent | exact GlobalTheory.clopen_image_irreducibleComponent | (intros; apply GlobalTheory.clopen_image_irreducibleComponent <;> assumption)
end _root_.GlobalTheory.T
