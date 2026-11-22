-- Prove2me | solution 1 for Nock.evalN_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:01.941069+00:00
-- url     : https://prove2.me/submissions/6182b675-c2db-4846-b3b8-c42f6b35b097

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Semantics

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution {n : Nat} {s form r : Noun}
    (h : evalN n s form = some r) : evalN (n + 1) s form = some r := by
  induction n, s, form using evalN.induct generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalN, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalN, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalN]
end Nock
