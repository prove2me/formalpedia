-- Prove2me | solution 1 for GlobalTheory.InvariantSupremum.eq_bot_or_eq_top_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:53:44.21572+00:00
-- url     : https://prove2.me/submissions/6f5bb87f-ffb5-46b5-b581-0f6ef7e7f84a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqBotOrEqTopOfInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantSupremum
namespace GlobalTheory.InvariantSupremum
theorem _root_.solution {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (P : Submodule ℂ W)
    (hP : ∀ g : G, ∀ w ∈ P, σ g w ∈ P) : P = ⊥ ∨ P = ⊤ := by
  let Q : Subrepresentation σ :=
    { toSubmodule := P
      apply_mem_toSubmodule := by
        intro g v hv
        exact hP g v hv }
  rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ hσ Q with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
end GlobalTheory.InvariantSupremum
