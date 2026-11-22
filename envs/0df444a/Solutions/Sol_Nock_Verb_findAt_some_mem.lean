-- Prove2me | solution 1 for Nock.Verb.findAt_some_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:00.400658+00:00
-- url     : https://prove2.me/submissions/2debaa3c-5e10-407f-a785-f6ae9a4a047d

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
theorem _root_.solution {i : Nat} {v : Verb} :
    ∀ {L : List (Nat × Verb)}, findAt i L = some v → (i, v) ∈ L
  | [],            h => by simp [findAt] at h
  | (j, w) :: t, h => by
      simp only [findAt] at h
      split at h
      · rename_i hij
        subst hij
        obtain rfl := Option.some.inj h
        simp
      · exact List.mem_cons_of_mem _ (solution h)
end Nock.Verb
