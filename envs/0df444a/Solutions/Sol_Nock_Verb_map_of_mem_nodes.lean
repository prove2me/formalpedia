-- Prove2me | solution 1 for Nock.Verb.map_of_mem_nodes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:07.700199+00:00
-- url     : https://prove2.me/submissions/9f6f50fb-5b5e-40c2-8561-cd1af865b9bc

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_enum_ge_start
public import Theorems.Thm_Nock_Verb_enum_index_range
public import Theorems.Thm_Nock_Verb_findAt_append
public import Theorems.Thm_Nock_Verb_findAt_eq_none
section
@[expose] public section
namespace Nock
namespace Verb
private theorem enum_findAt (v : Verb) (c : Nat) :
    ∀ p ∈ (enum v c).2, findAt p.1 (enum v c).2 = some p.2 := by
  induction v generalizing c with
  | leaf n => intro p hp; simp [enum] at hp
  | node a l r ihl ihr =>
      intro p hp
      simp only [enum, List.mem_cons, List.mem_append] at hp
      have hlge : c + 1 ≤ (enum l (c + 1)).1 := enum_ge_start l (c + 1)
      simp only [enum, findAt]
      rcases hp with hroot | hleft | hright
      · subst hroot; simp
      · have hb := enum_index_range l (c + 1) p hleft
        have hpc : p.1 ≠ c := by omega
        rw [if_neg hpc, findAt_append]
        rw [ihl (c + 1) p hleft]
      · have hb := enum_index_range r (enum l (c + 1)).1 p hright
        have hpc : p.1 ≠ c := by omega
        rw [if_neg hpc, findAt_append]
        have hnone : findAt p.1 (enum l (c + 1)).2 = none := by
          apply findAt_eq_none
          intro q hq
          have := enum_index_range l (c + 1) q hq
          omega
        rw [hnone]
        exact ihr (enum l (c + 1)).1 p hright
end Verb
end Nock
end
end

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {i : Nat} {v : Verb}
    (h : (i, v) ∈ nodes a) : map i a = some v :=
  enum_findAt a 0 (i, v) h
end Nock.Verb
