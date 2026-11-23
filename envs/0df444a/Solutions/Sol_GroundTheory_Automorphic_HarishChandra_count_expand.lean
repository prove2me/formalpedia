-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.count_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:43.326659+00:00
-- url     : https://prove2.me/submissions/fc6f2ae6-951f-438a-9d69-1ee344de01f6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_letters
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nodup_letters
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



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) (a : Fin n × Fin n) :
    Multiset.count a ((expand m : List _) : Multiset _) = m a := by
  have key : ∀ l : List (Fin n × Fin n), l.Nodup →
      Multiset.count a ((l.flatMap fun b => List.replicate (m b) b : List _) : Multiset _) =
        if a ∈ l then m a else 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons b l ih =>
      rw [List.flatMap_cons, ← Multiset.coe_add, Multiset.count_add, ih (List.nodup_cons.1 hl).2,
        Multiset.coe_replicate, Multiset.count_replicate]
      by_cases hb : b = a
      · subst hb; simp [(List.nodup_cons.1 hl).1]
      · simp [hb, Ne.symm hb]
  rw [expand, key _ nodup_letters, if_pos (mem_letters a)]
end GroundTheory.Automorphic.HarishChandra
