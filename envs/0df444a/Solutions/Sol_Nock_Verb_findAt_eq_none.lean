-- Prove2me | solution 1 for Nock.Verb.findAt_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:03.159803+00:00
-- url     : https://prove2.me/submissions/3cdc2884-deb3-4ec5-83d4-7ef762788a6b

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {i : Nat} :
    ∀ {L : List (Nat × Verb)}, (∀ p ∈ L, p.1 ≠ i) → findAt i L = none
  | [],            _ => rfl
  | (j, w) :: t, h => by
      have hj : ¬ (i = j) := fun heq => (h (j, w) (by simp)) heq.symm
      simp only [findAt, if_neg hj]
      exact solution (fun p hp => h p (List.mem_cons_of_mem _ hp))
end Nock.Verb
