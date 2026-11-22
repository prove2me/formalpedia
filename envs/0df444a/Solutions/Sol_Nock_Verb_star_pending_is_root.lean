-- Prove2me | solution 1 for Nock.Verb.star_pending_is_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:29.182677+00:00
-- url     : https://prove2.me/submissions/4e43a78c-b647-42ea-8e6a-4307cd672684

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_enum_nonpending_of_terminal
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {L R : Verb}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    {i : Nat} {sub : Verb}
    (hmap : map i (.node .star L R) = some sub) (hp : sub.isPending = true) :
    sub = .node .star L R := by
  have hmem : (i, sub) ∈ nodes (.node .star L R) := mem_nodes_of_map hmap
  simp only [nodes, enum, List.mem_cons, List.mem_append] at hmem
  rcases hmem with hz | hl | hr
  · exact (Prod.mk.injEq .. ▸ hz).2
  · exact absurd (enum_nonpending_of_terminal L hL 1 (i, sub) hl) (by rw [hp]; simp)
  · exact absurd (enum_nonpending_of_terminal R hR _ (i, sub) hr) (by rw [hp]; simp)
end Nock.Verb
