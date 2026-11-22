-- Prove2me | solution 1 for Nock.Verb.replaceAux_rel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:22.066288+00:00
-- url     : https://prove2.me/submissions/bb51d8a1-02cf-41ba-8e44-20df5770276c

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_replaceAux_counter
public import Theorems.Thm_Nock_Verb_enum_index_range
public import Theorems.Thm_Nock_Verb_findAt_append
public import Theorems.Thm_Nock_Verb_findAt_eq_none
public import Theorems.Thm_Nock_Verb_findAt_some_mem


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (i : Nat) (r₀ : Verb) :
    ∀ (v : Verb) (c : Nat),
      (∀ sub, findAt i (enum v c).2 = some sub →
        sub.isPending = true ∧ (∀ x, Den sub x ↔ Den r₀ x)) →
      Rel v (replaceAux i r₀ v c).2 := by
  intro v
  induction v with
  | leaf k => intro c _; exact Rel.leaf
  | node a l r ihl ihr =>
      intro c hyp
      simp only [replaceAux]
      by_cases hci : c = i
      · subst hci
        have hf : findAt c (enum (.node a l r) c).2 = some (.node a l r) := by
          simp [enum, findAt]
        obtain ⟨hp, hd⟩ := hyp _ hf
        rw [if_pos rfl]
        exact Rel.base hp hd
      · simp only [if_neg hci]
        have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c+1)).1 = (enum l (c+1)).1 := replaceAux_counter i r₀ l (c+1)
        refine Rel.cong (ihl (c+1) ?_) ?_
        · intro sub hsub
          apply hyp sub
          simp only [enum, findAt, if_neg hine]
          rw [findAt_append, hsub]
        · rw [hcL]
          apply ihr
          intro sub hsub
          apply hyp sub
          simp only [enum, findAt, if_neg hine]
          rw [findAt_append]
          have hnone : findAt i (enum l (c+1)).2 = none := by
            apply findAt_eq_none
            intro q hq
            have := enum_index_range l (c+1) q hq
            have := enum_index_range r (enum l (c+1)).1 (i, sub) (findAt_some_mem hsub)
            omega
          rw [hnone, hsub]
end Nock.Verb
