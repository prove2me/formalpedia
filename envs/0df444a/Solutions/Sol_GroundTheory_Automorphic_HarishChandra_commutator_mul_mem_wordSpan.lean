-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.commutator_mul_mem_wordSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:54.333132+00:00
-- url     : https://prove2.me/submissions/f90c2844-cff4-4319-a8cb-0c8e3e9c2f08

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_mem_wordSpan
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_sub_mul
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
theorem _root_.solution {P : Fin n × Fin n → Prop} (hP : Closed P)
    {a b : Fin n × Fin n} (ha : P a) (hb : P b) {l : List (Fin n × Fin n)} (hl : ∀ c ∈ l, P c) :
    (e a * e b - e b * e a) * word l ∈ wordSpan P (l.length + 1) := by
  rw [e_mul_sub_mul, sub_mul]
  refine Submodule.sub_mem _ ?_ ?_
  · split_ifs with h
    · rw [← word_cons]
      refine word_mem_wordSpan (w := (a.1, b.2) :: l) ?_
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hP a b ha hb h
      · exact hl c hc
    · simp
  · split_ifs with h
    · rw [← word_cons]
      refine word_mem_wordSpan (w := (b.1, a.2) :: l) ?_
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hP b a hb ha h
      · exact hl c hc
    · simp
end GroundTheory.Automorphic.HarishChandra
