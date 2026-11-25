-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_mem_canonSpan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:35.346796+00:00
-- url     : https://prove2.me/submissions/fbf0e748-d288-4e7f-8e4b-733a5e061a9f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_sub_word_mem_of_perm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_perm_expand
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_degree_toFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_support_toFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canonSpan_mono
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_canonSpan
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
theorem _root_.solution {P : Fin n × Fin n → Prop} (hP : Closed P) :
    ∀ (w : List (Fin n × Fin n)), (∀ a ∈ w, P a) →
      word w ∈ canonSpan P (min 1 w.length) w.length := by
  intro w
  induction hk : w.length using Nat.strong_induction_on generalizing w with
  | _ k ih =>
  intro hw
  set m := Multiset.toFinsupp (w : Multiset (Fin n × Fin n))
  have hmP : ∀ a ∈ m.support, P a := fun a ha => hw a (mem_of_mem_support_toFinsupp ha)
  have hmdeg : m.degree = k := by rw [degree_toFinsupp, hk]
  have hcanon : canon m ∈ canonSpan P (min 1 k) k := by
    have := canon_mem_canonSpan hmP
    rw [hmdeg] at this
    exact canonSpan_mono (min_le_right _ _) le_rfl this
  rw [← sub_add_cancel (word w) (canon m)]
  refine Submodule.add_mem _ ?_ hcanon
  have hperm := word_sub_word_mem_of_perm hP (perm_expand w) hw
  rw [hk] at hperm
  change word w - word (expand m) ∈ _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  ·
    have hw' : w = expand m := by
      rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
      · simp [m]
      · have h := perm_expand [a]
        exact (List.perm_singleton.1 h.symm).symm
      · simp at hk; omega
    rw [← hw', sub_self]
    exact Submodule.zero_mem _
  · refine (Submodule.span_le.2 ?_) hperm
    rintro _ ⟨v, hv, hvl, rfl⟩
    have := ih (k - 1) (by omega) v hvl hv
    rw [show min 1 (k - 1) = 1 by omega] at this
    exact canonSpan_mono (by omega) (by omega) this
end GroundTheory.Automorphic.HarishChandra
