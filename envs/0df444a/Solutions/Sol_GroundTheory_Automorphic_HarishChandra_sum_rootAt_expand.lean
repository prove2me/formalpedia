-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.sum_rootAt_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:53:34.374934+00:00
-- url     : https://prove2.me/submissions/970215b1-205b-41cb-a63c-c7f56492abd7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_toFinsupp_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) (k : Fin n) :
    ((expand m).map fun a => rootAt a k).sum = wt m k := by
  have hw : ∀ w : List (Fin n × Fin n), (w.map fun a => rootAt a k).sum =
      wt (Multiset.toFinsupp (w : Multiset _)) k := by
    intro w
    induction w with
    | nil => simp [wt]
    | cons a w ih =>
      rw [List.map_cons, List.sum_cons, ih,
        show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, wt, wt,
        Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring),
        Finsupp.sum_single_index (by simp)]
      push_cast; ring
  rw [hw, toFinsupp_expand]
end GroundTheory.Automorphic.HarishChandra
