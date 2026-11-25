-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_sub_word_mem_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:47.427689+00:00
-- url     : https://prove2.me/submissions/c2f5d67f-cfda-4707-b0dd-b7ac36bd0d2c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemOfMemSupportToFinsupp
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_e_mul_mem_wordSpan
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_commutator_mul_mem_wordSpan
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
theorem _root_.solution {P : Fin n × Fin n → Prop} (hP : Closed P)
    {w w' : List (Fin n × Fin n)} (h : w.Perm w') (hw : ∀ a ∈ w, P a) :
    word w - word w' ∈ wordSpan P (w.length - 1) := by
  induction h with
  | nil => simp
  | cons x h ih =>
    rename_i l₁ l₂
    rcases l₁ with _ | ⟨y, l₁⟩
    · rw [List.nil_perm.1 h]; simp
    · rw [show word (x :: y :: l₁) - word (x :: l₂) = e x * (word (y :: l₁) - word l₂) by
        rw [word_cons x, word_cons x, mul_sub], List.length_cons, Nat.add_sub_cancel]
      have := ih fun a ha => hw a (List.mem_cons_of_mem _ ha)
      simp only [List.length_cons, Nat.add_sub_cancel] at this
      exact e_mul_mem_wordSpan (hw x (List.mem_cons_self ..)) this
  | swap x y l =>
    rw [word_cons, word_cons, word_cons, word_cons, ← mul_assoc, ← mul_assoc, ← sub_mul]
    simp only [List.length_cons, Nat.add_sub_cancel]
    exact commutator_mul_mem_wordSpan hP (hw y (by simp)) (hw x (by simp))
      (fun c hc => hw c (by simp [hc]))
  | trans h₁ h₂ ih₁ ih₂ =>
    rw [← sub_add_sub_cancel]
    refine Submodule.add_mem _ (ih₁ hw) ?_
    rw [h₁.length_eq]
    exact ih₂ fun a ha => hw a (h₁.symm.subset ha)
end GroundTheory.Automorphic.HarishChandra
