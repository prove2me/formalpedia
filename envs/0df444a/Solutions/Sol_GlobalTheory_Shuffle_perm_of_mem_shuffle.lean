-- Prove2me | solution 1 for GlobalTheory.Shuffle.perm_of_mem_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:39.444695+00:00
-- url     : https://prove2.me/submissions/c008fc18-dc51-474d-9dfc-8e2f91ee8071

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
theorem _root_.solution : ∀ (u v w : List A), w ∈ shuffle u v → w.Perm (u ++ v)
  | [], v, w, h => by simp at h; simp [h]
  | a :: u, [], w, h => by simp at h; simp [h]
  | a :: u, b :: v, w, h => by
      rw [shuffle_cons_cons, Multiset.mem_add, Multiset.mem_map, Multiset.mem_map] at h
      rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · exact (solution u (b :: v) x hx).cons a
      · exact ((solution (a :: u) v x hx).cons b).trans List.perm_middle.symm
end GlobalTheory.Shuffle
