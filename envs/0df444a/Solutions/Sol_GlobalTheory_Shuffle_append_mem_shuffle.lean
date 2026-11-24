-- Prove2me | solution 1 for GlobalTheory.Shuffle.append_mem_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:48:02.769827+00:00
-- url     : https://prove2.me/submissions/d366b953-e563-442b-b386-1f0c27f6e0e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.Shuffle
variable {A : Type}
namespace GlobalTheory.Shuffle
theorem _root_.solution : ∀ (u v : List A), u ++ v ∈ shuffle u v
  | [], v => by simp
  | a :: u, [] => by simp
  | a :: u, b :: v => by
      rw [shuffle_cons_cons, Multiset.mem_add]
      exact Or.inl (Multiset.mem_map.2 ⟨_, solution u (b :: v), rfl⟩)
end GlobalTheory.Shuffle
