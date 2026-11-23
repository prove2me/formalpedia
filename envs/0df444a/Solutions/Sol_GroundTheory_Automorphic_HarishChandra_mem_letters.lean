-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.mem_letters
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:13.552443+00:00
-- url     : https://prove2.me/submissions/351b9f3a-5ca7-44e5-ba43-b225278220d2

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
theorem _root_.solution (a : Fin n × Fin n) : a ∈ letters n := by
  simp only [letters, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and, decide_eq_true_eq]
  have hall : ∃ i, ∃ j, (i, j) = a := ⟨a.1, a.2, rfl⟩
  rcases lt_trichotomy a.1 a.2 with h | h | h
  · exact Or.inr ⟨hall, h⟩
  · exact Or.inl (Or.inr ⟨hall, h⟩)
  · exact Or.inl (Or.inl ⟨hall, h⟩)
end GroundTheory.Automorphic.HarishChandra
