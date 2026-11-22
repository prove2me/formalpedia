-- Prove2me | solution 1 for Nock.Verb.editOk_enum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:38.616705+00:00
-- url     : https://prove2.me/submissions/3500beeb-bda4-4b56-94be-f4123bf53f05

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_editOk_children

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution : ∀ (v : Verb) (c : Nat), editOk v = true →
    ∀ p ∈ (enum v c).2, editOk p.2 = true := by
  intro v
  induction v with
  | leaf k => intro c _ p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro c hok p hp
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      simp only [enum, List.mem_cons, List.mem_append] at hp
      rcases hp with rfl | hpl | hpr
      · exact hok
      · exact ihl (c+1) hokl p hpl
      · exact ihr _ hokr p hpr
end Nock.Verb
