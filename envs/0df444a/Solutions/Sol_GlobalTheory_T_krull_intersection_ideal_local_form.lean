-- Prove2me | solution 1 for GlobalTheory.T.krull_intersection_ideal_local_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:20.546331+00:00
-- url     : https://prove2.me/submissions/1930e7e9-40aa-4b7d-b88c-0771d7a0ce07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullIntersectionIdealLocalForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullIntersectionIdealLocalFormStatement
import Theorems.Thm_GlobalTheory_krull_inter_ideal_local


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
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  first | exact @GlobalTheory.krull_inter_ideal_local | exact GlobalTheory.krull_inter_ideal_local | (intros; apply GlobalTheory.krull_inter_ideal_local <;> assumption)
end _root_.GlobalTheory.T
