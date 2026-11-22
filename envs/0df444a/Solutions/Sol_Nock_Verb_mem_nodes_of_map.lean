-- Prove2me | solution 1 for Nock.Verb.mem_nodes_of_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:27.270295+00:00
-- url     : https://prove2.me/submissions/c72fd69d-5b22-4eec-84ec-8e39984cf14a

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_findAt_some_mem

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a : Verb} {i : Nat} {v : Verb}
    (h : map i a = some v) : (i, v) ∈ nodes a :=
  findAt_some_mem h
end Nock.Verb
