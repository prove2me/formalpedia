-- Prove2me | solution 1 for GlobalTheory.T.mem_closure_of_forall_clm_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:52.95147+00:00
-- url     : https://prove2.me/submissions/c8239633-ecb7-4a6d-9344-011a0216c223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemClosureOfForallDualVanish
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemClosureOfForallDualVanishStatement
import Theorems.Thm_GlobalTheory_mem_closure_of_forall_dual_vanish


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
theorem _root_.solution : ∀ {E : Type} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    {p : ℕ → Seminorm ℂ E}, WithSeminorms p → ∀ (Z : Submodule ℂ E) (x : E),
    (∀ f : E →L[ℂ] ℂ, (∀ z ∈ Z, f z = 0) → f x = 0) → x ∈ closure (Z : Set E) := by
  first | exact @GlobalTheory.mem_closure_of_forall_dual_vanish | exact GlobalTheory.mem_closure_of_forall_dual_vanish | (intros; apply GlobalTheory.mem_closure_of_forall_dual_vanish <;> assumption)
end _root_.GlobalTheory.T
