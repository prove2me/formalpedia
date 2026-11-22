-- Prove2me | solution 1 for Nock.evalPaper_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:02.509811+00:00
-- url     : https://prove2.me/submissions/0743d2e0-fb72-444e-b3eb-f353dc39c1ca

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_PaperReference

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {n : Nat} {s form r : Noun}
    (h : evalPaper n s form = some r) : evalPaper (n + 1) s form = some r := by
  induction n, s, form using evalPaper.induct generalizing r with
  | case11 fuel subj tail ih =>
      simp only [evalPaper, Option.map_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | case12 fuel subj tail ih =>
      simp only [evalPaper, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨a, ha, hp⟩ := h
      exact ⟨a, ih ha, hp⟩
  | _ =>
      simp_all [evalPaper]
end Nock
