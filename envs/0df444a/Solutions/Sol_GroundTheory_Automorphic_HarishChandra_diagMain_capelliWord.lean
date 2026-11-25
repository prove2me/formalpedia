-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.diagMain_capelliWord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:19:47.945905+00:00
-- url     : https://prove2.me/submissions/99fec34f-a63a-4858-b691-408fed57d833

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_const_of_forall_rotate
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProj0_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
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
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcProj0_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {k : ℕ} (i : Fin (k + 1) → Fin n) :
    diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
      ∑ c : Fin n, if i = (fun _ => c) then X c ^ (k + 1) else 0 := by
  classical
  by_cases h : ∀ t, i t = i (finRotate (k + 1) t)
  · have hc := const_of_forall_rotate h
    have hall : ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))),
        a.1 = a.2 := by
      intro a ha
      obtain ⟨t, rfl⟩ := List.mem_ofFn.1 ha
      exact h t
    rw [diagMain, if_pos hall, List.map_ofFn, List.prod_ofFn]
    rw [Finset.sum_eq_single (i 0)]
    · rw [if_pos (funext hc)]
      simp only [Function.comp_apply, hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · intro c _ hc'
      rw [if_neg]
      intro he
      exact hc' (by rw [he])
    · simp
  · have hnot : ¬ ∀ a ∈ List.ofFn (fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))),
        a.1 = a.2 := by
      intro hall
      exact h fun t => hall _ (List.mem_ofFn.2 ⟨t, rfl⟩)
    rw [diagMain, if_neg hnot]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro rfl
    exact h fun t => rfl
end GroundTheory.Automorphic.HarishChandra
