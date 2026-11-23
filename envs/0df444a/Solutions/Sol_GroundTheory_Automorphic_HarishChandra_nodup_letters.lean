-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.nodup_letters
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:14.340803+00:00
-- url     : https://prove2.me/submissions/8a7a4e36-0d4e-4791-aae5-464eff5dfa8d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
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



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution : (letters n).Nodup := by
  have hall : ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => (List.nodup_finRange n).map fun j j' h => by simpa using h, ?_⟩
    refine (List.nodup_finRange n).pairwise_of_forall_ne ?_
    intro i _ i' _ hii'
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨j, rfl⟩ ⟨j', h⟩
    exact hii' (congrArg Prod.fst h).symm
  simp only [letters]
  refine List.Nodup.append (List.Nodup.append (hall.filter _) (hall.filter _) ?_) (hall.filter _) ?_
  · simp only [List.disjoint_left, List.mem_filter, decide_eq_true_eq]
    rintro a ⟨_, h⟩ ⟨_, h'⟩
    exact absurd h (by rw [h']; exact lt_irrefl _)
  · simp only [List.disjoint_left, List.mem_append, List.mem_filter, decide_eq_true_eq]
    rintro a (⟨_, h⟩ | ⟨_, h⟩) ⟨_, h'⟩
    · exact lt_asymm h h'
    · exact absurd h' (by rw [h]; exact lt_irrefl _)
end GroundTheory.Automorphic.HarishChandra
