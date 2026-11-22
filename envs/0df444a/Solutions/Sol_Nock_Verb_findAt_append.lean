-- Prove2me | solution 1 for Nock.Verb.findAt_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:40.103254+00:00
-- url     : https://prove2.me/submissions/b6522521-7a28-4c80-8638-9c8f253ec496

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
theorem _root_.solution (i : Nat) :
    ∀ (L1 L2 : List (Nat × Verb)),
      findAt i (L1 ++ L2) = match findAt i L1 with
                            | some v => some v
                            | none   => findAt i L2
 := by
  intro L1 L2
  induction L1 with
  | nil => simp [findAt]
  | cons p t ih =>
      rcases p with ⟨j, w⟩
      simp only [List.cons_append, findAt]
      by_cases h : i = j
      · simp [h]
      · simp only [if_neg h]; exact ih
end Nock.Verb
