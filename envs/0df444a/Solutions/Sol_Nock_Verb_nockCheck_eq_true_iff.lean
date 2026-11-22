-- Prove2me | solution 1 for Nock.Verb.nockCheck_eq_true_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:53.597376+00:00
-- url     : https://prove2.me/submissions/27bfbcee-8b2f-4221-930e-9034eba8d07e

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_map_some_of_getIndex

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔
      (∃ v, b = some v ∧ next a = some v) ∨ (b = none ∧ Crashes a) := by
  unfold NockCheck Crashes
  cases hgi : getIndex a with
  | none =>
      have hn : next a = none := by unfold next; rw [hgi]
      rw [hn]; simp
  | some i =>
      obtain ⟨Fi, hmap⟩ := map_some_of_getIndex hgi
      simp only [hmap]
      by_cases hd : inDomain Fi = true
      · cases hr : reduce Fi with
        | some Fnext =>
            have hnext : next a = some (replaceAt i a Fnext) := by
              unfold next; simp only [hgi, hmap, if_pos hd, hr]
            simp only [hd]
            constructor
            · intro h
              have hb : b = some (replaceAt i a Fnext) := by simpa using h
              exact Or.inl ⟨_, hb, hnext⟩
            · rintro (⟨v, hb, hv⟩ | ⟨_, _, hcr⟩)
              · rw [hnext] at hv
                have : v = replaceAt i a Fnext := (Option.some.inj hv).symm
                subst this; simp [hb]
              · rw [hnext] at hcr; simp at hcr
        | none =>
            have hnext : next a = none := by
              unfold next; simp only [hgi, hmap, if_pos hd, hr]
            simp only [hd]
            constructor
            · intro h
              have hb : b = none := by simpa using h
              exact Or.inr ⟨hb, by simp, hnext⟩
            · rintro (⟨v, hb, hv⟩ | ⟨hb, _, _⟩)
              · rw [hnext] at hv; simp at hv
              · simp [hb]
      · have hd' : inDomain Fi = false := by simpa using hd
        have hnext : next a = none := by
          unfold next; simp only [hgi, hmap, if_neg hd]
        simp only [hd']
        constructor
        · intro h
          have hb : b = none := by simpa using h
          exact Or.inr ⟨hb, by simp, hnext⟩
        · rintro (⟨v, hb, hv⟩ | ⟨hb, _, _⟩)
          · rw [hnext] at hv; simp at hv
          · simp [hb]
end Nock.Verb
