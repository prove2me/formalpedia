-- Prove2me | solution 1 for Nock.Verb.enum_index_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:44.9498+00:00
-- url     : https://prove2.me/submissions/e82377cd-78d2-4f31-a21f-410ca71bfa7d

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_enum_ge_start

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, c ≤ p.1 ∧ p.1 < (enum v c).1 := by
  induction v generalizing c with
  | leaf n => intro p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro p hp
      simp only [enum, List.mem_cons, List.mem_append] at hp
      have hlge : c + 1 ≤ (enum l (c + 1)).1 := enum_ge_start l (c + 1)
      have hrge : (enum l (c + 1)).1 ≤ (enum r (enum l (c + 1)).1).1 := enum_ge_start r _
      rcases hp with hroot | hleft | hright
      · subst hroot; simp only [enum]; omega
      · have := ihl (c + 1) p hleft
        simp only [enum]; omega
      · have := ihr (enum l (c + 1)).1 p hright
        simp only [enum]; omega
end Nock.Verb
