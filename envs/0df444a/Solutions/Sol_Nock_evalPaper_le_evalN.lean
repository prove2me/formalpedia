-- Prove2me | solution 1 for Nock.evalPaper_le_evalN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:11.069119+00:00
-- url     : https://prove2.me/submissions/5a615757-44ed-4a8c-ab7a-ad96788816e9

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
    (h : evalPaper n s form = some r) : evalN n s form = some r := by
  induction n, s, form using evalPaper.induct generalizing r <;>
    simp_all only [evalPaper, evalN, Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.some.injEq, reduceCtorEq] <;>
    grind
end Nock
